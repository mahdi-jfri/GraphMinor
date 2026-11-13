module

public import Mathlib.Tactic.Linarith
public import GraphMinor.Compute.Algorithm81
public import GraphMinor.Compute.Algorithm65
public import GraphMinor.Compute.Bridge13

/-!
# Graph Minors XIII, Algorithm (8.3) on the Word RAM

This file implements Algorithm (8.3) of Robertson and Seymour, *Graph Minors. XIII.
The Disjoint Paths Problem*, J. Combin. Theory Ser. B 63 (1995), 65–110 (pages 93–94),
on the Word RAM model (`Cmd` in `GraphMinor/Compute/Basic.lean`).

## The Paper's Algorithm (8.3)

From GM XIII, Section 8, pages 93–94:

> A **separation** of a core $C$ is a pair $(A, B)$ of subgraphs with $A \cup B = C$ and
> $E(A \cap B) = \emptyset$; and its **order** is $|V(A \cap B)|$. A vertex $v$ of $C$ is
> **4-linked** (in $C$) if there is no separation $(A, B)$ of $C$ of order $\le 3$ with
> $v \in V(A) \setminus V(B)$ and $\Omega \subseteq V(B)$. A core $C$ is **4-linked** if every
> vertex of $C$ is 4-linked in $C$.
>
> **(8.2)** Let $C$ be a core in $(G, \Omega)$, and suppose $v \in V(C)$ is not 4-linked in $C$.
> Let $(A, B)$ be a separation of $C$ of minimum order such that $v \in V(A) \setminus V(B)$
> and $\Omega \subseteq V(B)$. Let $C'$ be obtained from $B$ by adding an edge joining each pair of
> non-adjacent vertices in $V(A \cap B)$. Then
> (1) for every separation $(A', B')$ of $C$ with $v \in V(A') \setminus V(B')$ and
>     $\Omega \subseteq V(B')$, if $|V(A' \cap B')| = |V(A \cap B)|$ and $A \subseteq A'$ then $A' = A$;
> (2) $C'$ is a core;
> (3) for every $Z \subseteq \Omega$ with $|Z| \le 4$, the $Z$-folios of $C$ and $C'$ have the same
>     realizable members; and
> (4) every vertex of $C'$ which was 4-linked in $C$ is also 4-linked in $C'$.
>
> **(8.3) Algorithm.**
> - **Input:** A society $(G, \Omega)$.
> - **Output:** A 4-linked core $C$ in $(G, \Omega)$.
> - **Running time:** $O(v\varepsilon)$.
>
> **Description.** Initially we set $C = G$. Now we examine each vertex $v$ of $G$ in turn. If
> $v \notin V(C)$ we move directly to the next vertex. If $v \in V(C)$, we test if $v$ is 4-linked
> in $C$, using flows cleanly in time $O(\varepsilon)$; and if not, we find a separation $(A, B)$
> of $C$ of minimum order with $v \in V(A) \setminus V(B)$ and $\Omega \subseteq V(B)$, and replace
> $C$ by $C'$ as defined in (8.2). (Notice that $|E(C')| \le |E(C)| + 3$, and so execution of one of
> these steps takes time $O(\varepsilon)$, since $|E(C)|$ never exceeds $\varepsilon + 3v$.) After
> examining each vertex we output $C$ and stop. Since the operation of replacing $C$ by $C'$
> preserves the property of being 4-linked, by (8.2)(4), it follows that the output graph $C$ is
> indeed a 4-linked core.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ## Section 1: Mathematical Specification of Cores, 4-Linkedness, (8.2), and Traces -/

/-- A vertex-level separation `(A, B)` of a core `(Z, C)` on vertex set `Z ⊆ Fin n`:
`A, B ⊆ Z`, `A ∪ B = Z`, and there is no edge of `C` between `A \ B` and `B \ A`.
(Any edge inside `A ∩ B` is assigned to `A` or `B` so `E(A ∩ B) = ∅`.) -/
def IsCoreSeparation {n : ℕ} (Z : Finset (Fin n)) (C : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) : Prop :=
  A ⊆ Z ∧ B ⊆ Z ∧ A ∪ B = Z ∧ ∀ u ∈ A \ B, ∀ w ∈ B \ A, ¬ C.Adj u w

/-- A vertex `v` is 4-linked in the core `(Z, C)` with boundary `omega` if there is no
separation `(A, B)` of `(Z, C)` of order `|A ∩ B| ≤ 3` with `v ∈ A \ B` and `Ω ⊆ B`
(GM XIII, page 93). -/
def IsFourLinkedAt {n : ℕ} (omega : List (Fin n)) (Z : Finset (Fin n))
    (C : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∀ A B : Finset (Fin n), IsCoreSeparation Z C A B →
    (A ∩ B).card ≤ 3 → omega.toFinset ⊆ B → v ∉ A \ B

/-- A core `(Z, C)` is 4-linked if every vertex `v ∈ Z` is 4-linked in `(Z, C)` (GM XIII, page 93). -/
def IsFourLinkedCore {n : ℕ} (omega : List (Fin n)) (Z : Finset (Fin n))
    (C : SimpleGraph (Fin n)) : Prop :=
  omega.toFinset ⊆ Z ∧ (∀ u w, C.Adj u w → u ∈ Z ∧ w ∈ Z) ∧
    ∀ v ∈ Z, IsFourLinkedAt omega Z C v

/-- A separation `(A, B)` of `(Z, C)` is a minimum-order separation separating `v` from `Ω`
as required by the hypotheses of `(8.2)` (GM XIII, page 93): `(A, B)` is a separation of `(Z, C)`
of order `≤ 3` with `v ∈ A \ B` and `Ω ⊆ B`, and every separation `(A', B')` of `(Z, C)` with
`v ∈ A' \ B'` and `Ω ⊆ B'` has `|A ∩ B| ≤ |A' ∩ B'|`. -/
def IsMinOrderCoreSeparation {n : ℕ} (omega : List (Fin n)) (Z : Finset (Fin n))
    (C : SimpleGraph (Fin n)) (v : Fin n) (A B : Finset (Fin n)) : Prop :=
  IsCoreSeparation Z C A B ∧
    v ∈ A \ B ∧
    omega.toFinset ⊆ B ∧
    (A ∩ B).card ≤ 3 ∧
    ∀ A' B' : Finset (Fin n), IsCoreSeparation Z C A' B' →
      v ∈ A' \ B' → omega.toFinset ⊆ B' → (A ∩ B).card ≤ (A' ∩ B').card

/-- The graph `C'` obtained from `(Z, C)` and a separation `(A, B)` in `(8.2)` (GM XIII, page 93):
restrict `C` to `B` and add an edge joining each pair of distinct vertices in `A ∩ B`. -/
def coreStepGraph {n : ℕ} (C : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    SimpleGraph (Fin n) where
  Adj u w := u ∈ B ∧ w ∈ B ∧ u ≠ w ∧ (C.Adj u w ∨ (u ∈ A ∩ B ∧ w ∈ A ∩ B))
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.1.symm,
    h.2.2.2.imp (fun hadj => hadj.symm) (fun hmem => ⟨hmem.2, hmem.1⟩)⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

instance instDecidableRelCoreStepGraphAdj {n : ℕ} (C : SimpleGraph (Fin n))
    [DecidableRel C.Adj] (A B : Finset (Fin n)) :
    DecidableRel (coreStepGraph C A B).Adj :=
  fun u w => inferInstanceAs
    (Decidable (u ∈ B ∧ w ∈ B ∧ u ≠ w ∧ (C.Adj u w ∨ (u ∈ A ∩ B ∧ w ∈ A ∩ B))))

lemma coreStepGraph_adj_mem {n : ℕ} {C : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {u w : Fin n} (h : (coreStepGraph C A B).Adj u w) : u ∈ B ∧ w ∈ B :=
  ⟨h.1, h.2.1⟩

/-- In `coreStepGraph C A B`, any separation `(A', B')` of `B` must contain the clique `A ∩ B`
entirely inside `A'` or entirely inside `B'`. -/
lemma coreStepGraph_clique_side {n : ℕ} {C : SimpleGraph (Fin n)} {A B A' B' : Finset (Fin n)}
    (hsep' : IsCoreSeparation B (coreStepGraph C A B) A' B') :
    A ∩ B ⊆ A' ∨ A ∩ B ⊆ B' := by
  by_contra hnot
  rcases not_or.mp hnot with ⟨hnotA', hnotB'⟩
  rcases Finset.not_subset.mp hnotA' with ⟨u, huAB, huNotA'⟩
  rcases Finset.not_subset.mp hnotB' with ⟨w, hwAB, hwNotB'⟩
  have huB : u ∈ B := (Finset.mem_inter.mp huAB).2
  have hwB : w ∈ B := (Finset.mem_inter.mp hwAB).2
  have huB' : u ∈ B' := by
    have huU : u ∈ A' ∪ B' := hsep'.2.2.1.symm ▸ huB
    exact (Finset.mem_union.mp huU).resolve_left huNotA'
  have hwA' : w ∈ A' := by
    have hwU : w ∈ A' ∪ B' := hsep'.2.2.1.symm ▸ hwB
    exact (Finset.mem_union.mp hwU).resolve_right hwNotB'
  have hne : w ≠ u := by
    intro heq
    subst heq
    exact hwNotB' huB'
  have hadj : (coreStepGraph C A B).Adj w u :=
    ⟨hwB, huB, hne, Or.inr ⟨hwAB, huAB⟩⟩
  exact hsep'.2.2.2 w (Finset.mem_sdiff.mpr ⟨hwA', hwNotB'⟩)
    u (Finset.mem_sdiff.mpr ⟨huB', huNotA'⟩) hadj

/-- Claim (4) of `(8.2)` (GM XIII, page 93): every vertex `v' ∈ B` which was 4-linked in `(Z, C)`
is also 4-linked in `(B, coreStepGraph C A B)`. -/
theorem isFourLinkedAt_coreStepGraph {n : ℕ} {omega : List (Fin n)}
    {Z : Finset (Fin n)} {C : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    (hsep : IsCoreSeparation Z C A B)
    {v' : Fin n} (hlinked : IsFourLinkedAt omega Z C v') :
    IsFourLinkedAt omega B (coreStepGraph C A B) v' := by
  intro A' B' hsep' hcard' homega' hv'
  rcases coreStepGraph_clique_side hsep' with hsubA' | hsubB'
  · -- Case 1: A ∩ B ⊆ A'. Then (A ∪ A', B') is a separation of (Z, C) with intersection A' ∩ B'.
    have hsep_ext : IsCoreSeparation Z C (A ∪ A') B' := by
      refine ⟨Finset.union_subset hsep.1 (hsep'.1.trans hsep.2.1), hsep'.2.1.trans hsep.2.1, ?_, ?_⟩
      · calc
          (A ∪ A') ∪ B' = A ∪ (A' ∪ B') := Finset.union_assoc A A' B'
          _ = A ∪ B := by rw [hsep'.2.2.1]
          _ = Z := hsep.2.2.1
      · intro u hu w hw hadj
        have huU : u ∈ A ∪ A' := (Finset.mem_sdiff.mp hu).1
        have huNotB' : u ∉ B' := (Finset.mem_sdiff.mp hu).2
        have hwB' : w ∈ B' := (Finset.mem_sdiff.mp hw).1
        have hwNotAA' : w ∉ A ∪ A' := (Finset.mem_sdiff.mp hw).2
        have hwNotA : w ∉ A := fun h => hwNotAA' (Finset.mem_union_left A' h)
        have hwNotA' : w ∉ A' := fun h => hwNotAA' (Finset.mem_union_right A h)
        have hwB : w ∈ B := hsep'.2.1 hwB'
        rcases Finset.mem_union.mp huU with huA | huA'
        · by_cases huB : u ∈ B
          · have huAB : u ∈ A ∩ B := Finset.mem_inter.mpr ⟨huA, huB⟩
            have huA' : u ∈ A' := hsubA' huAB
            have hne : u ≠ w := fun heq => huNotB' (heq ▸ hwB')
            exact hsep'.2.2.2 u (Finset.mem_sdiff.mpr ⟨huA', huNotB'⟩)
              w (Finset.mem_sdiff.mpr ⟨hwB', hwNotA'⟩)
              ⟨huB, hwB, hne, Or.inl hadj⟩
          · exact hsep.2.2.2 u (Finset.mem_sdiff.mpr ⟨huA, huB⟩)
              w (Finset.mem_sdiff.mpr ⟨hwB, hwNotA⟩) hadj
        · have huB : u ∈ B := hsep'.1 huA'
          have hne : u ≠ w := fun heq => huNotB' (heq ▸ hwB')
          exact hsep'.2.2.2 u (Finset.mem_sdiff.mpr ⟨huA', huNotB'⟩)
            w (Finset.mem_sdiff.mpr ⟨hwB', hwNotA'⟩)
            ⟨huB, hwB, hne, Or.inl hadj⟩
    have hinter_eq : (A ∪ A') ∩ B' = A' ∩ B' := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxA | hxA', hxB'⟩
        · exact ⟨hsubA' (Finset.mem_inter.mpr ⟨hxA, hsep'.2.1 hxB'⟩), hxB'⟩
        · exact ⟨hxA', hxB'⟩
      · rintro ⟨hxA', hxB'⟩
        exact ⟨Or.inr hxA', hxB'⟩
    have hv'_ext : v' ∈ (A ∪ A') \ B' := by
      rw [Finset.mem_sdiff] at hv' ⊢
      exact ⟨Finset.mem_union_right A hv'.1, hv'.2⟩
    exact hlinked (A ∪ A') B' hsep_ext (hinter_eq.symm ▸ hcard') homega' hv'_ext
  · -- Case 2: A ∩ B ⊆ B'. Then (A', A ∪ B') is a separation of (Z, C) with intersection A' ∩ B'.
    have hsep_ext : IsCoreSeparation Z C A' (A ∪ B') := by
      refine ⟨hsep'.1.trans hsep.2.1, Finset.union_subset hsep.1 (hsep'.2.1.trans hsep.2.1), ?_, ?_⟩
      · calc
          A' ∪ (A ∪ B') = A ∪ (A' ∪ B') := by
            rw [← Finset.union_assoc, Finset.union_comm A' A, Finset.union_assoc]
          _ = A ∪ B := by rw [hsep'.2.2.1]
          _ = Z := hsep.2.2.1
      · intro u hu w hw hadj
        have huA' : u ∈ A' := (Finset.mem_sdiff.mp hu).1
        have huNotAB' : u ∉ A ∪ B' := (Finset.mem_sdiff.mp hu).2
        have huNotA : u ∉ A := fun h => huNotAB' (Finset.mem_union_left B' h)
        have huNotB' : u ∉ B' := fun h => huNotAB' (Finset.mem_union_right A h)
        have huB : u ∈ B := hsep'.1 huA'
        have hwU : w ∈ A ∪ B' := (Finset.mem_sdiff.mp hw).1
        have hwNotA' : w ∉ A' := (Finset.mem_sdiff.mp hw).2
        rcases Finset.mem_union.mp hwU with hwA | hwB'
        · by_cases hwB : w ∈ B
          · have hwAB : w ∈ A ∩ B := Finset.mem_inter.mpr ⟨hwA, hwB⟩
            have hwB' : w ∈ B' := hsubB' hwAB
            have hne : u ≠ w := fun heq => huNotB' (heq ▸ hwB')
            exact hsep'.2.2.2 u (Finset.mem_sdiff.mpr ⟨huA', huNotB'⟩)
              w (Finset.mem_sdiff.mpr ⟨hwB', hwNotA'⟩)
              ⟨huB, hwB, hne, Or.inl hadj⟩
          · exact hsep.2.2.2 w (Finset.mem_sdiff.mpr ⟨hwA, hwB⟩)
              u (Finset.mem_sdiff.mpr ⟨huB, huNotA⟩) hadj.symm
        · have hwB : w ∈ B := hsep'.2.1 hwB'
          have hne : u ≠ w := fun heq => huNotB' (heq ▸ hwB')
          exact hsep'.2.2.2 u (Finset.mem_sdiff.mpr ⟨huA', huNotB'⟩)
            w (Finset.mem_sdiff.mpr ⟨hwB', hwNotA'⟩)
            ⟨huB, hwB, hne, Or.inl hadj⟩
    have hinter_eq : A' ∩ (A ∪ B') = A' ∩ B' := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxA', hxA | hxB'⟩
        · exact ⟨hxA', hsubB' (Finset.mem_inter.mpr ⟨hxA, hsep'.1 hxA'⟩)⟩
        · exact ⟨hxA', hxB'⟩
      · rintro ⟨hxA', hxB'⟩
        exact ⟨hxA', Or.inr hxB'⟩
    have hv'B : v' ∈ B := hsep'.1 (Finset.mem_sdiff.mp hv').1
    have hv'NotA : v' ∉ A := fun hv'A =>
      (Finset.mem_sdiff.mp hv').2 (hsubB' (Finset.mem_inter.mpr ⟨hv'A, hv'B⟩))
    have hv'_ext : v' ∈ A' \ (A ∪ B') := by
      rw [Finset.mem_sdiff, Finset.mem_union, not_or]
      exact ⟨(Finset.mem_sdiff.mp hv').1, hv'NotA, (Finset.mem_sdiff.mp hv').2⟩
    have homega_ext : omega.toFinset ⊆ A ∪ B' :=
      homega'.trans (Finset.subset_union_right)
    exact hlinked A' (A ∪ B') hsep_ext (hinter_eq.symm ▸ hcard') homega_ext hv'_ext

/-- Four paths from `v` to `Ω` in `(Z, C)` that are pairwise vertex-disjoint except at `v`,
witnessing that `v` is 4-linked in `(Z, C)`. -/
structure FourLinkedPaths {n : ℕ} (omega : List (Fin n)) (Z : Finset (Fin n))
    (C : SimpleGraph (Fin n)) (v : Fin n) where
  u : Fin 4 → Fin n
  P : ∀ i : Fin 4, C.Walk v (u i)
  hu_mem : ∀ i : Fin 4, u i ∈ omega.toFinset
  hpath : ∀ i : Fin 4, (P i).IsPath
  hsupp_Z : ∀ i : Fin 4, ∀ x ∈ (P i).support, x ∈ Z
  hdisj : ∀ i j : Fin 4, i ≠ j → List.Disjoint (P i).support.tail (P j).support.tail

/-- Any walk in `C` starting in `A \ B` and ending in `B` under a separation `(A, B)` of `(Z, C)`
whose vertices lie in `Z` must contain a vertex of `A ∩ B` in its tail support. -/
lemma walk_meets_core_sep_inter {n : ℕ} {Z : Finset (Fin n)} {C : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} (hsep : IsCoreSeparation Z C A B)
    {u w : Fin n} (p : C.Walk u w) (hu : u ∈ A \ B) (hw : w ∈ B)
    (hZ : ∀ x ∈ p.support, x ∈ Z) :
    ∃ x ∈ p.support.tail, x ∈ A ∩ B := by
  induction p with
  | nil =>
    exfalso
    exact (Finset.mem_sdiff.mp hu).2 hw
  | @cons u y w hadj q ih =>
    have hyZ : y ∈ Z := hZ y (by simp)
    by_cases hyB : y ∈ B
    · by_cases hyA : y ∈ A
      · exact ⟨y, by simp, Finset.mem_inter.mpr ⟨hyA, hyB⟩⟩
      · exfalso
        exact hsep.2.2.2 u hu y (Finset.mem_sdiff.mpr ⟨hyB, hyA⟩) hadj
    · have hyA : y ∈ A := by
        have hyU : y ∈ A ∪ B := hsep.2.2.1.symm ▸ hyZ
        exact (Finset.mem_union.mp hyU).resolve_right hyB
      rcases ih (Finset.mem_sdiff.mpr ⟨hyA, hyB⟩) hw (fun x hx => hZ x (by simp [hx])) with
        ⟨x, hx_tail, hxAB⟩
      exact ⟨x, List.mem_of_mem_tail hx_tail, hxAB⟩

/-- If `v` has four paths to `Ω` in `(Z, C)` (`FourLinkedPaths omega Z C v`), then `v` is
4-linked in `(Z, C)`. -/
theorem isFourLinkedAt_of_fourLinkedPaths {n : ℕ} {omega : List (Fin n)}
    {Z : Finset (Fin n)} {C : SimpleGraph (Fin n)} {v : Fin n}
    (fp : FourLinkedPaths omega Z C v) :
    IsFourLinkedAt omega Z C v := by
  intro A B hsep hcard homega hv
  have hex : ∀ i : Fin 4, ∃ x ∈ (fp.P i).support.tail, x ∈ A ∩ B := by
    intro i
    exact walk_meets_core_sep_inter hsep (fp.P i) hv (homega (fp.hu_mem i)) (fp.hsupp_Z i)
  choose f hf_tail hf_AB using hex
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact fp.hdisj i j hne (hf_tail i) (hij ▸ hf_tail j)
  have hsub : Finset.image f Finset.univ ⊆ A ∩ B := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact hf_AB i
  have hcard4 : 4 ≤ (A ∩ B).card := by
    calc
      4 = (Finset.univ : Finset (Fin 4)).card := by simp
      _ = (Finset.image f Finset.univ).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (A ∩ B).card := Finset.card_le_card hsub
  omega

/-- If `v ∈ Z` and `v ∈ omega.toFinset`, then four trivial paths of length 0 at `v`
give `FourLinkedPaths omega Z C v`. -/
def fourLinkedPaths_of_mem_omega {n : ℕ} {omega : List (Fin n)}
    {Z : Finset (Fin n)} {C : SimpleGraph (Fin n)} {v : Fin n}
    (hvZ : v ∈ Z) (hvOmega : v ∈ omega.toFinset) :
    FourLinkedPaths omega Z C v where
  u _ := v
  P _ := .nil
  hu_mem _ := hvOmega
  hpath _ := Walk.IsPath.nil
  hsupp_Z _ x hx := by
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ hvZ
  hdisj _ _ _ := by
    simp [Walk.support_nil]

/-- Lift a walk in `restrictGraph C Y` to a walk in `C` with the same support. -/
def liftRestrictWalk {n : ℕ} {C : SimpleGraph (Fin n)} {Y : Finset (Fin n)}
    {u w : Fin n} : (restrictGraph C Y).Walk u w → C.Walk u w
  | .nil => .nil
  | .cons h p => .cons ((restrictGraph_adj C Y _ _).mp h).2.2 (liftRestrictWalk p)

@[simp]
lemma support_liftRestrictWalk {n : ℕ} {C : SimpleGraph (Fin n)} {Y : Finset (Fin n)}
    {u w : Fin n} (p : (restrictGraph C Y).Walk u w) :
    (liftRestrictWalk p).support = p.support := by
  induction p with
  | nil => rfl
  | cons _ p ih => simp [liftRestrictWalk, ih]

lemma isPath_liftRestrictWalk {n : ℕ} {C : SimpleGraph (Fin n)} {Y : Finset (Fin n)}
    {u w : Fin n} {p : (restrictGraph C Y).Walk u w} (hp : p.IsPath) :
    (liftRestrictWalk p).IsPath := by
  rw [Walk.isPath_def, support_liftRestrictWalk]
  exact hp.support_nodup

lemma mem_Y_of_mem_support_restrictWalk {n : ℕ} {C : SimpleGraph (Fin n)} {Y : Finset (Fin n)}
    {u w : Fin n} (p : (restrictGraph C Y).Walk u w) (hu : u ∈ Y)
    {x : Fin n} (hx : x ∈ p.support) : x ∈ Y := by
  induction p with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ hu
  | cons h q ih =>
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx_q
    · exact hu
    · exact ih ((restrictGraph_adj C Y _ _).mp h).2.1 hx_q

lemma mem_Z_of_mem_support_restrictWalk {n : ℕ} {C : SimpleGraph (Fin n)} {Y Z : Finset (Fin n)}
    (hC_Z : ∀ a b, C.Adj a b → a ∈ Z ∧ b ∈ Z)
    {u w : Fin n} (p : (restrictGraph C Y).Walk u w) (hu : u ∈ Z)
    {x : Fin n} (hx : x ∈ p.support) : x ∈ Z := by
  induction p with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ hu
  | cons h q ih =>
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx_q
    · exact hu
    · exact ih (hC_Z _ _ ((restrictGraph_adj C Y _ _).mp h).2.2).2 hx_q

/-- When Menger finds a path system of size 4 in `restrictGraph C (Finset.univ \ {v})`
from `extNeighborhood C {v}` to `omega.toFinset`, prepending `v` yields `FourLinkedPaths omega Z C v`. -/
noncomputable def fourLinkedPaths_of_menger {n : ℕ} {omega : List (Fin n)}
    {Z : Finset (Fin n)} {C : SimpleGraph (Fin n)} [DecidableRel C.Adj]
    (hC_Z : ∀ a b, C.Adj a b → a ∈ Z ∧ b ∈ Z)
    {v : Fin n} (hvZ : v ∈ Z)
    {used pred succ : Fin n → ℕ}
    (hvps : IsValidPathSystem (restrictGraph C (Finset.univ \ {v}))
      (extNeighborhood C {v}) omega.toFinset used pred succ)
    (hcard4 : (pathStarts used pred).card = 4) :
    FourLinkedPaths omega Z C v := by
  classical
  let W := extractDisjointPaths hvps hcard4
  have hsound := extractDisjointPaths_sound hvps hcard4
  have hadj_v : ∀ i : Fin 4, C.Adj v (W i).start := by
    intro i
    have hs := (W i).start_mem
    rw [mem_extNeighborhood] at hs
    rcases hs.2 with ⟨x, hx, hadj⟩
    rw [Finset.mem_singleton] at hx
    exact hx ▸ hadj
  have hv_not_mem : ∀ i : Fin 4, v ∉ (W i).walk.support := by
    intro i hmem
    have hs_mem_ext := (W i).start_mem
    rw [mem_extNeighborhood] at hs_mem_ext
    have hs_Y : (W i).start ∈ Finset.univ \ {v} := by
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, hs_mem_ext.1⟩
    have hv_Y := mem_Y_of_mem_support_restrictWalk (W i).walk hs_Y hmem
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hv_Y
    exact hv_Y.2 rfl
  exact {
    u := fun i => (W i).finish
    P := fun i => Walk.cons (hadj_v i) (liftRestrictWalk (W i).walk)
    hu_mem := fun i => (W i).finish_mem
    hpath := fun i => by
      refine Walk.IsPath.cons (isPath_liftRestrictWalk (hsound.2 i)) ?_
      rw [support_liftRestrictWalk]
      exact hv_not_mem i
    hsupp_Z := fun i x hx => by
      simp only [Walk.support_cons, support_liftRestrictWalk, List.mem_cons] at hx
      rcases hx with rfl | hx_p
      · exact hvZ
      · exact mem_Z_of_mem_support_restrictWalk hC_Z (W i).walk
          (hC_Z _ _ (hadj_v i)).2 hx_p
    hdisj := fun i j hij => by
      simp only [Walk.support_cons, List.tail_cons, support_liftRestrictWalk]
      exact hsound.1 i j hij
  }

/-- Any walk in `C` from `u ∈ A'` to `w ∈ B'` under a separation `(A', B')` of `(Z, C)`
whose vertices lie in `Z` contains a vertex of `A' ∩ B'` in its support. -/
lemma walk_meets_core_sep_support {n : ℕ} {Z : Finset (Fin n)} {C : SimpleGraph (Fin n)}
    {A' B' : Finset (Fin n)} (hsep : IsCoreSeparation Z C A' B')
    {u w : Fin n} (p : C.Walk u w) (hu : u ∈ A') (hw : w ∈ B')
    (hZ : ∀ x ∈ p.support, x ∈ Z) :
    ∃ z ∈ A' ∩ B', z ∈ p.support := by
  by_cases huB' : u ∈ B'
  · exact ⟨u, Finset.mem_inter.mpr ⟨hu, huB'⟩, Walk.start_mem_support p⟩
  · rcases walk_meets_core_sep_inter hsep p (Finset.mem_sdiff.mpr ⟨hu, huB'⟩) hw hZ with
      ⟨z, hz_tail, hzAB⟩
    exact ⟨z, hzAB, List.mem_of_mem_tail hz_tail⟩

/-- For any separation `(A', B')` of `(Z, C)` with `v ∈ A' \ B'` and `omega.toFinset ⊆ B'`,
its separator `A' ∩ B'` is an `(extNeighborhood C {v}, omega.toFinset)`-separator in
`restrictGraph C (Finset.univ \ {v})`. -/
lemma isABSeparator_of_coreSeparation {n : ℕ} {omega : List (Fin n)}
    {Z : Finset (Fin n)} {C : SimpleGraph (Fin n)}
    (hC_Z : ∀ a b, C.Adj a b → a ∈ Z ∧ b ∈ Z)
    {v : Fin n} {A' B' : Finset (Fin n)}
    (hsep : IsCoreSeparation Z C A' B')
    (hv : v ∈ A' \ B') (homega : omega.toFinset ⊆ B') :
    IsABSeparator (restrictGraph C (Finset.univ \ {v}))
      (extNeighborhood C {v}) omega.toFinset (A' ∩ B') := by
  intro w
  have hs_ext := w.start_mem
  rw [mem_extNeighborhood] at hs_ext
  rcases hs_ext.2 with ⟨x, hx, hadj_vx⟩
  rw [Finset.mem_singleton] at hx
  have hadj_vw : C.Adj v w.start := hx ▸ hadj_vx
  have hsZ : w.start ∈ Z := (hC_Z v w.start hadj_vw).2
  have hsA' : w.start ∈ A' := by
    by_contra hsNotA'
    have hsB' : w.start ∈ B' := by
      have hsU : w.start ∈ A' ∪ B' := hsep.2.2.1.symm ▸ hsZ
      exact (Finset.mem_union.mp hsU).resolve_left hsNotA'
    exact hsep.2.2.2 v hv w.start (Finset.mem_sdiff.mpr ⟨hsB', hsNotA'⟩) hadj_vw
  have htB' : w.finish ∈ B' := homega w.finish_mem
  have hsupp_Z : ∀ z ∈ (liftRestrictWalk w.walk).support, z ∈ Z := by
    rw [support_liftRestrictWalk]
    exact fun z hz => mem_Z_of_mem_support_restrictWalk hC_Z w.walk hsZ hz
  rcases walk_meets_core_sep_support hsep (liftRestrictWalk w.walk) hsA' htB' hsupp_Z with
    ⟨z, hzAB, hz_supp⟩
  rw [support_liftRestrictWalk] at hz_supp
  exact ⟨z, hzAB, hz_supp⟩

/-- When Menger stops at order `≤ 3` on `restrictGraph C (Finset.univ \ {v})` from
`extNeighborhood C {v}` to `omega.toFinset`, the candidate separation
`(alg62VA {v} items, alg62VB {v} items)` restricted to `Z` gives `A = Z ∩ VB` and `B = Z ∩ VA`
satisfying `IsMinOrderCoreSeparation` and `¬ IsFourLinkedAt omega Z C v`. -/
theorem minOrderCoreSeparation_of_menger {n : ℕ} {omega : List (Fin n)}
    {Z : Finset (Fin n)} {C : SimpleGraph (Fin n)} [DecidableRel C.Adj]
    (homega_Z : omega.toFinset ⊆ Z)
    (hC_Z : ∀ a b, C.Adj a b → a ∈ Z ∧ b ∈ Z)
    {v : Fin n} (hvZ : v ∈ Z) (hvNotOmega : v ∉ omega.toFinset)
    {used pred succ : Fin n → ℕ} {items : List ℕ}
    (hsys : IsValidPathSystem (restrictGraph C (Finset.univ \ {v}))
      (extNeighborhood C {v}) omega.toFinset used pred succ)
    (hcard_le : (pathStarts used pred).card ≤ 3)
    (hinit : ∀ a ∈ extNeighborhood C {v}, a.1 ∈ items)
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items →
      ResidualAdj (restrictGraph C (Finset.univ \ {v})) used pred succ x y → y.1 ∈ items)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj (restrictGraph C (Finset.univ \ {v})) used pred succ)
        {x | ∃ a ∈ extNeighborhood C {v}, x = inNode a} z)
    (hnoB : ∀ b ∈ omega.toFinset, b.1 + n ∉ items) :
    let A := Z ∩ alg62VB {v} items
    let B := Z ∩ alg62VA {v} items
    IsMinOrderCoreSeparation omega Z C v A B ∧ ¬ IsFourLinkedAt omega Z C v ∧
      A ∩ B = alg62VA {v} items ∩ alg62VB {v} items := by
  intro A B
  have hcore_sep : IsCoreSeparation Z C A B := by
    refine ⟨Finset.inter_subset_left, Finset.inter_subset_left, ?_, ?_⟩
    · ext x
      simp only [A, B, Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hxZ, _⟩ | ⟨hxZ, _⟩) <;> exact hxZ
      · intro hxZ
        have hxU : x ∈ alg62VA {v} items ∪ alg62VB {v} items := by
          rw [alg62VA_union_alg62VB hsys hinit hclosed hreach]; exact Finset.mem_univ x
        rcases Finset.mem_union.mp hxU with hxVA | hxVB
        · exact Or.inr ⟨hxZ, hxVA⟩
        · exact Or.inl ⟨hxZ, hxVB⟩
    · intro u hu w hw hadj
      have huVB : u ∈ alg62VB {v} items := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hu).1).2
      have huZ : u ∈ Z := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hu).1).1
      have huNotVA : u ∉ alg62VA {v} items := fun huVA =>
        (Finset.mem_sdiff.mp hu).2 (Finset.mem_inter.mpr ⟨huZ, huVA⟩)
      have hwVA : w ∈ alg62VA {v} items := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw).1).2
      have hwZ : w ∈ Z := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw).1).1
      have hwNotVB : w ∉ alg62VB {v} items := fun hwVB =>
        (Finset.mem_sdiff.mp hw).2 (Finset.mem_inter.mpr ⟨hwZ, hwVB⟩)
      rw [mem_alg62VA] at hwVA huNotVA
      rw [mem_alg62VB] at huVB hwNotVB
      push Not at huNotVA hwNotVB
      rcases huVB with huv | hu_in_items
      · have hw_ext : w ∈ extNeighborhood C {v} :=
          (mem_extNeighborhood C {v} w).mpr ⟨hwVA.1, u, huv, hadj⟩
        exact hwNotVB.2 (hinit w hw_ext)
      · have huNotX : u ∉ ({v} : Finset (Fin n)) :=
          fun h => (not_mem_items_of_mem_X hsys hreach h).1 hu_in_items
        have hu_out : u.1 + n ∈ items := huNotVA huNotX
        have hadj' : (restrictGraph C (Finset.univ \ {v})).Adj u w := by
          rw [restrictGraph_adj]
          exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huNotX⟩,
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwVA.1⟩, hadj⟩
        exact hwNotVB.2 (inNode_mem_of_outNode_mem_of_adj hsys hinit hclosed hreach hu_out hadj')
  have hv_AB : v ∈ A \ B := by
    have hv_X : v ∈ ({v} : Finset (Fin n)) := Finset.mem_singleton_self v
    have hv_sdiff := subset_alg62VB_sdiff ({v} : Finset (Fin n)) items hv_X
    rw [Finset.mem_sdiff] at hv_sdiff ⊢
    refine ⟨Finset.mem_inter.mpr ⟨hvZ, hv_sdiff.1⟩, ?_⟩
    intro hvB
    exact hv_sdiff.2 (Finset.mem_inter.mp hvB).2
  have hdisj_omega_v : Disjoint omega.toFinset ({v} : Finset (Fin n)) :=
    Finset.disjoint_singleton_right.mpr hvNotOmega
  have homega_VA : omega.toFinset ⊆ alg62VA {v} items :=
    subset_alg62VA hdisj_omega_v hnoB
  have homega_B : omega.toFinset ⊆ B :=
    Finset.subset_inter homega_Z homega_VA
  have hinter_sub : A ∩ B ⊆ alg62VA {v} items ∩ alg62VB {v} items := by
    intro x hx
    simp only [A, B, Finset.mem_inter] at hx ⊢
    exact ⟨hx.2.2, hx.1.2⟩
  have hcard_VAVB : (alg62VA {v} items ∩ alg62VB {v} items).card ≤ (pathStarts used pred).card := by
    rw [alg62VA_inter_alg62VB hsys hreach]
    exact card_resCut_le_card_pathStarts hsys hclosed
  have hcard_AB_le_3 : (A ∩ B).card ≤ 3 :=
    (Finset.card_le_card hinter_sub).trans (hcard_VAVB.trans hcard_le)
  have hmin_starts : ∀ A' B' : Finset (Fin n), IsCoreSeparation Z C A' B' →
      v ∈ A' \ B' → omega.toFinset ⊆ B' → (pathStarts used pred).card ≤ (A' ∩ B').card := by
    intro A' B' hsep' hv' homega'
    exact card_pathStarts_le_of_isABSeparator hsys
      (isABSeparator_of_coreSeparation hC_Z hsep' hv' homega')
  have hmin : ∀ A' B' : Finset (Fin n), IsCoreSeparation Z C A' B' →
      v ∈ A' \ B' → omega.toFinset ⊆ B' → (A ∩ B).card ≤ (A' ∩ B').card := by
    intro A' B' hsep' hv' homega'
    exact (Finset.card_le_card hinter_sub).trans
      (hcard_VAVB.trans (hmin_starts A' B' hsep' hv' homega'))
  have hcard_AB_ge : (pathStarts used pred).card ≤ (A ∩ B).card :=
    hmin_starts A B hcore_sep hv_AB homega_B
  have hinter_eq : A ∩ B = alg62VA {v} items ∩ alg62VB {v} items :=
    Finset.eq_of_subset_of_card_le hinter_sub (le_trans hcard_VAVB hcard_AB_ge)
  have hmin_order : IsMinOrderCoreSeparation omega Z C v A B :=
    ⟨hcore_sep, hv_AB, homega_B, hcard_AB_le_3, hmin⟩
  have hnot_linked : ¬ IsFourLinkedAt omega Z C v :=
    fun hlinked => hlinked A B hcore_sep hcard_AB_le_3 homega_B hv_AB
  exact ⟨hmin_order, hnot_linked, hinter_eq⟩

/-- Ordered pairs `(K[i], K[j])` with `i < j` for a list `K : List (Fin n)` of length `≤ 3`. -/
def cliquePairs {n : ℕ} (K : List (Fin n)) : List (Fin n × Fin n) :=
  (if h1 : 1 < K.length then [(K[0]'(by omega), K[1]'h1)] else []) ++
  (if h2 : 2 < K.length then [(K[0]'(by omega), K[2]'h2), (K[1]'(by omega), K[2]'h2)] else [])

lemma length_cliquePairs_le {n : ℕ} (K : List (Fin n)) :
    (cliquePairs K).length ≤ 3 := by
  dsimp [cliquePairs]
  split_ifs <;> simp

lemma mem_cliquePairs_endpoints {n : ℕ} {K : List (Fin n)} {p : Fin n × Fin n}
    (hp : p ∈ cliquePairs K) : p.1 ∈ K ∧ p.2 ∈ K := by
  dsimp [cliquePairs] at hp
  rcases List.mem_append.mp hp with h1 | h2
  · split_ifs at h1 with hk1
    · simp only [List.mem_singleton] at h1
      subst h1
      exact ⟨List.getElem_mem _, List.getElem_mem _⟩
    · simp at h1
  · split_ifs at h2 with hk2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with rfl | rfl <;> exact ⟨List.getElem_mem _, List.getElem_mem _⟩
    · simp at h2

lemma cliquePairs_no_self_loop {n : ℕ} {K : List (Fin n)} (hnodup : K.Nodup)
    (k : ℕ) (hk : k < (cliquePairs K).length) :
    ((cliquePairs K)[k]'hk).1 ≠ ((cliquePairs K)[k]'hk).2 := by
  have hget : ∀ i j (hi : i < K.length) (hj : j < K.length), i ≠ j → K[i]'hi ≠ K[j]'hj := by
    intro i j hi hj hne heq
    exact hne ((List.Nodup.getElem_inj_iff hnodup).mp heq)
  by_cases h2 : 2 < K.length
  · have h1 : 1 < K.length := by omega
    have hcp : cliquePairs K =
        [(K[0]'(by omega), K[1]'h1), (K[0]'(by omega), K[2]'h2), (K[1]'h1, K[2]'h2)] := by
      simp [cliquePairs, h1, h2]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by rw [hcp] at hk; simp at hk; omega) with
      rfl | rfl | rfl
    · simp only [hcp, List.getElem_cons_zero]
      exact hget 0 1 (by omega) h1 (by omega)
    · simp only [hcp, List.getElem_cons_succ, List.getElem_cons_zero]
      exact hget 0 2 (by omega) h2 (by omega)
    · simp only [hcp, List.getElem_cons_succ, List.getElem_cons_zero]
      exact hget 1 2 h1 h2 (by omega)
  · by_cases h1 : 1 < K.length
    · have hcp : cliquePairs K = [(K[0]'(by omega), K[1]'h1)] := by
        simp [cliquePairs, h1, h2]
      have hk0 : k = 0 := by rw [hcp] at hk; simp at hk; omega
      subst hk0
      simp only [hcp, List.getElem_cons_zero]
      exact hget 0 1 (by omega) h1 (by omega)
    · simp [cliquePairs, h1, h2] at hk

lemma cliquePairs_no_dup {n : ℕ} {K : List (Fin n)} (hnodup : K.Nodup)
    (i j : ℕ) (hij : i < j) (hj : j < (cliquePairs K).length) :
    ¬((((cliquePairs K)[i]'(by omega)).1 = ((cliquePairs K)[j]'hj).1 ∧
       ((cliquePairs K)[i]'(by omega)).2 = ((cliquePairs K)[j]'hj).2) ∨
      (((cliquePairs K)[i]'(by omega)).1 = ((cliquePairs K)[j]'hj).2 ∧
       ((cliquePairs K)[i]'(by omega)).2 = ((cliquePairs K)[j]'hj).1)) := by
  have hinj : ∀ a b (ha : a < K.length) (hb : b < K.length), K[a]'ha = K[b]'hb → a = b :=
    fun a b ha hb h => (List.Nodup.getElem_inj_iff hnodup).mp h
  by_cases h2 : 2 < K.length
  · have h1 : 1 < K.length := by omega
    have hcp : cliquePairs K =
        [(K[0]'(by omega), K[1]'h1), (K[0]'(by omega), K[2]'h2), (K[1]'h1, K[2]'h2)] := by
      simp [cliquePairs, h1, h2]
    rcases (show (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) by
        rw [hcp] at hj; simp at hj; omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [hcp, List.getElem_cons_succ, List.getElem_cons_zero]
      rintro (⟨_, h12⟩ | ⟨h02, _⟩)
      · have := hinj 1 2 h1 h2 h12; omega
      · have := hinj 0 2 (by omega) h2 h02; omega
    · simp only [hcp, List.getElem_cons_succ, List.getElem_cons_zero]
      rintro (⟨h01, _⟩ | ⟨h02, _⟩)
      · have := hinj 0 1 (by omega) h1 h01; omega
      · have := hinj 0 2 (by omega) h2 h02; omega
    · simp only [hcp, List.getElem_cons_succ, List.getElem_cons_zero]
      rintro (⟨h01, _⟩ | ⟨_, h21⟩)
      · have := hinj 0 1 (by omega) h1 h01; omega
      · have := hinj 2 1 h2 h1 h21; omega
  · by_cases h1 : 1 < K.length
    · have hcp : cliquePairs K = [(K[0]'(by omega), K[1]'h1)] := by
        simp [cliquePairs, h1, h2]
      rw [hcp] at hj; simp at hj; omega
    · simp [cliquePairs, h1, h2] at hj

lemma exists_cliquePairs_of_mem {n : ℕ} {K : List (Fin n)}
    (hlen : K.length ≤ 3) {u w : Fin n} (hu : u ∈ K) (hw : w ∈ K) (hne : u ≠ w) :
    ∃ (k : ℕ) (hk : k < (cliquePairs K).length),
      (((cliquePairs K)[k]'hk).1 = u ∧ ((cliquePairs K)[k]'hk).2 = w) ∨
      (((cliquePairs K)[k]'hk).1 = w ∧ ((cliquePairs K)[k]'hk).2 = u) := by
  rcases List.mem_iff_getElem.mp hu with ⟨i, hi, rfl⟩
  rcases List.mem_iff_getElem.mp hw with ⟨j, hj, rfl⟩
  have hij_ne : i ≠ j := fun h => hne (by subst h; rfl)
  by_cases h2 : 2 < K.length
  · have h1 : 1 < K.length := by omega
    have hcp : cliquePairs K =
        [(K[0]'(by omega), K[1]'h1), (K[0]'(by omega), K[2]'h2), (K[1]'h1, K[2]'h2)] := by
      simp [cliquePairs, h1, h2]
    rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 2) ∨
        (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) by omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, by simp [hcp], Or.inl ⟨by simp [hcp], by simp [hcp]⟩⟩
    · exact ⟨0, by simp [hcp], Or.inr ⟨by simp [hcp], by simp [hcp]⟩⟩
    · exact ⟨1, by simp [hcp], Or.inl ⟨by simp [hcp], by simp [hcp]⟩⟩
    · exact ⟨1, by simp [hcp], Or.inr ⟨by simp [hcp], by simp [hcp]⟩⟩
    · exact ⟨2, by simp [hcp], Or.inl ⟨by simp [hcp], by simp [hcp]⟩⟩
    · exact ⟨2, by simp [hcp], Or.inr ⟨by simp [hcp], by simp [hcp]⟩⟩
  · have h1 : 1 < K.length := by omega
    have hcp : cliquePairs K = [(K[0]'(by omega), K[1]'h1)] := by
      simp [cliquePairs, h1, h2]
    rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, by simp [hcp], Or.inl ⟨by simp [hcp], by simp [hcp]⟩⟩
    · exact ⟨0, by simp [hcp], Or.inr ⟨by simp [hcp], by simp [hcp]⟩⟩

/-- Predicate selecting the edges of `C` kept during a core step `(A, B)`:
endpoints lie in `B` and do not both lie in `A ∩ B` (since `A ∩ B` is replaced by `cliquePairs`). -/
def keepCoreEdge {n : ℕ} (A B : Finset (Fin n)) (e : Fin n × Fin n) : Bool :=
  decide (e.1 ∈ B ∧ e.2 ∈ B ∧ ¬(e.1 ∈ A ∩ B ∧ e.2 ∈ A ∩ B))

/-- Updated simple edge list for `coreStepGraph C A B`. -/
def coreStepEdges {n : ℕ} (A B : Finset (Fin n)) (edges : List (Fin n × Fin n)) :
    List (Fin n × Fin n) :=
  edges.filter (keepCoreEdge A B) ++ cliquePairs ((List.finRange n).filter (· ∈ A ∩ B))

lemma length_coreStepEdges_le {n : ℕ} (A B : Finset (Fin n)) (edges : List (Fin n × Fin n)) :
    (coreStepEdges A B edges).length ≤ edges.length + 3 := by
  rw [coreStepEdges, List.length_append]
  exact Nat.add_le_add (List.length_filter_le _ _) (length_cliquePairs_le _)

lemma length_filter_finRange_eq_card {n : ℕ} (S : Finset (Fin n)) :
    ((List.finRange n).filter (· ∈ S)).length = S.card := by
  have hnodup : ((List.finRange n).filter (· ∈ S)).Nodup :=
    (List.nodup_finRange n).filter _
  have htoFinset : ((List.finRange n).filter (· ∈ S)).toFinset = S := by
    ext x
    simp
  calc
    ((List.finRange n).filter (· ∈ S)).length =
        ((List.finRange n).filter (· ∈ S)).toFinset.card :=
      (List.toFinset_card_of_nodup hnodup).symm
    _ = S.card := by rw [htoFinset]

/-- If `edges` is a valid simple edge list for `C` and `(A ∩ B).card ≤ 3`, then
`coreStepEdges A B edges` is a valid simple edge list for `coreStepGraph C A B`. -/
theorem isSimpleEdgeList_coreStepEdges {n : ℕ} {C : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList C edges)
    {A B : Finset (Fin n)} (hcard : (A ∩ B).card ≤ 3) :
    IsSimpleEdgeList (coreStepGraph C A B) (coreStepEdges A B edges) := by
  let L₁ := edges.filter (keepCoreEdge A B)
  let K := (List.finRange n).filter (· ∈ A ∩ B)
  let L₂ := cliquePairs K
  have hK_nodup : K.Nodup := (List.nodup_finRange n).filter _
  have hK_len : K.length ≤ 3 := by
    dsimp [K]
    rw [length_filter_finRange_eq_card]
    exact hcard
  have hK_mem : ∀ x : Fin n, x ∈ K ↔ x ∈ A ∩ B := by
    intro x
    simp [K, List.mem_filter]
  have hL₁_mem : ∀ e ∈ L₁, e ∈ edges ∧ e.1 ∈ B ∧ e.2 ∈ B ∧ ¬(e.1 ∈ A ∩ B ∧ e.2 ∈ A ∩ B) := by
    intro e he
    simp only [L₁, List.mem_filter, keepCoreEdge, decide_eq_true_eq] at he
    exact ⟨he.1, he.2⟩
  have hL₂_mem : ∀ e ∈ L₂, e.1 ∈ A ∩ B ∧ e.2 ∈ A ∩ B := by
    intro e he
    rcases mem_cliquePairs_endpoints he with ⟨h1, h2⟩
    exact ⟨(hK_mem e.1).mp h1, (hK_mem e.2).mp h2⟩
  have hsub : L₁.Sublist edges := List.filter_sublist
  rcases List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub with ⟨f, hf_get⟩
  change IsSimpleEdgeList (coreStepGraph C A B) (L₁ ++ L₂)
  refine ⟨?_, ?_, ?_⟩
  · -- 1. No self-loops
    intro k hk
    by_cases hk₁ : k < L₁.length
    · rw [List.getElem_append_left hk₁]
      have hfeq := hf_get ⟨k, hk₁⟩
      simp only [List.get_eq_getElem] at hfeq
      rw [hfeq]
      exact hedges.1 (f ⟨k, hk₁⟩).1 (f ⟨k, hk₁⟩).2
    · have hk₂ : k - L₁.length < L₂.length := by
        rw [List.length_append] at hk; omega
      rw [List.getElem_append_right (Nat.le_of_not_lt hk₁)]
      exact cliquePairs_no_self_loop hK_nodup (k - L₁.length) hk₂
  · -- 2. No duplicate undirected edges
    intro i j hij hj
    by_cases hj₁ : j < L₁.length
    · have hi₁ : i < L₁.length := by omega
      rw [List.getElem_append_left hi₁, List.getElem_append_left hj₁]
      have hfi := hf_get ⟨i, hi₁⟩
      have hfj := hf_get ⟨j, hj₁⟩
      simp only [List.get_eq_getElem] at hfi hfj
      rw [hfi, hfj]
      have hflt : (f ⟨i, hi₁⟩).1 < (f ⟨j, hj₁⟩).1 :=
        f.strictMono ( Fin.mk_lt_mk.mpr hij )
      exact hedges.2.1 (f ⟨i, hi₁⟩).1 (f ⟨j, hj₁⟩).1 hflt (f ⟨j, hj₁⟩).2
    · by_cases hi₁ : i < L₁.length
      · -- i in L₁, j in L₂: impossible since L₁ edges are not both in A ∩ B, while L₂ edges are
        rw [List.getElem_append_left hi₁, List.getElem_append_right (Nat.le_of_not_lt hj₁)]
        have hi_not := (hL₁_mem (L₁[i]'hi₁) (List.getElem_mem _)).2.2.2
        have hj₂ : j - L₁.length < L₂.length := by rw [List.length_append] at hj; omega
        have hj_in := hL₂_mem (L₂[j - L₁.length]'hj₂) (List.getElem_mem _)
        rintro (⟨heq1, heq2⟩ | ⟨heq1, heq2⟩)
        · exact hi_not ⟨heq1 ▸ hj_in.1, heq2 ▸ hj_in.2⟩
        · exact hi_not ⟨heq1 ▸ hj_in.2, heq2 ▸ hj_in.1⟩
      · -- Both i and j in L₂
        have hi₂ : i - L₁.length < L₂.length := by rw [List.length_append] at hj; omega
        have hj₂ : j - L₁.length < L₂.length := by rw [List.length_append] at hj; omega
        rw [List.getElem_append_right (Nat.le_of_not_lt hi₁),
            List.getElem_append_right (Nat.le_of_not_lt hj₁)]
        exact cliquePairs_no_dup hK_nodup (i - L₁.length) (j - L₁.length) (by omega) hj₂
  · -- 3. Adjacency equivalence
    intro u w
    constructor
    · rintro ⟨huB, hwB, hne, hadj | ⟨huAB, hwAB⟩⟩
      · by_cases hboth : u ∈ A ∩ B ∧ w ∈ A ∩ B
        · rcases exists_cliquePairs_of_mem hK_len ((hK_mem u).mpr hboth.1)
            ((hK_mem w).mpr hboth.2) hne with ⟨k, hk, hpair⟩
          have hk' : k < L₂.length := hk
          refine ⟨L₁.length + k, by rw [List.length_append]; omega, ?_⟩
          rw [List.getElem_append_right (by omega)]
          simpa using hpair
        · rcases (hedges.2.2 u w).mp hadj with ⟨k₀, hk₀, hpair₀⟩
          have hkeep : keepCoreEdge A B (edges[k₀]'hk₀) = true := by
            simp only [keepCoreEdge, decide_eq_true_eq]
            rcases hpair₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨huB, hwB, hboth⟩
            · exact ⟨hwB, huB, fun h => hboth ⟨h.2, h.1⟩⟩
          have hmem₁ : edges[k₀]'hk₀ ∈ L₁ :=
            List.mem_filter.mpr ⟨List.getElem_mem _, hkeep⟩
          rcases List.mem_iff_getElem.mp hmem₁ with ⟨k₁, hk₁, heq₁⟩
          refine ⟨k₁, by rw [List.length_append]; omega, ?_⟩
          rw [List.getElem_append_left hk₁, heq₁]
          exact hpair₀
      · rcases exists_cliquePairs_of_mem hK_len ((hK_mem u).mpr huAB)
          ((hK_mem w).mpr hwAB) hne with ⟨k, hk, hpair⟩
        have hk' : k < L₂.length := hk
        refine ⟨L₁.length + k, by rw [List.length_append]; omega, ?_⟩
        rw [List.getElem_append_right (by omega)]
        simpa using hpair
    · rintro ⟨k, hk, hpair⟩
      by_cases hk₁ : k < L₁.length
      · rw [List.getElem_append_left hk₁] at hpair
        have hmem := hL₁_mem (L₁[k]'hk₁) (List.getElem_mem _)
        rcases List.mem_iff_getElem.mp hmem.1 with ⟨k₀, hk₀, heq₀⟩
        have hadj : C.Adj u w := by
          rw [hedges.2.2 u w]
          refine ⟨k₀, hk₀, ?_⟩
          rw [heq₀]
          exact hpair
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hmem.2.1, hmem.2.2.1, C.ne_of_adj hadj, Or.inl hadj⟩
        · exact ⟨hmem.2.2.1, hmem.2.1, C.ne_of_adj hadj, Or.inl hadj⟩
      · have hk₂ : k - L₁.length < L₂.length := by rw [List.length_append] at hk; omega
        rw [List.getElem_append_right (Nat.le_of_not_lt hk₁)] at hpair
        have hmem := hL₂_mem (L₂[k - L₁.length]'hk₂) (List.getElem_mem _)
        have hne_idx := cliquePairs_no_self_loop hK_nodup (k - L₁.length) hk₂
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨(Finset.mem_inter.mp hmem.1).2, (Finset.mem_inter.mp hmem.2).2,
            hne_idx, Or.inr hmem⟩
        · exact ⟨(Finset.mem_inter.mp hmem.2).2, (Finset.mem_inter.mp hmem.1).2,
            hne_idx.symm, Or.inr ⟨hmem.2, hmem.1⟩⟩

/-- Inductive trace of Algorithm (8.3) from the initial core `(Finset.univ, x.G)` to `(Z, C)`,
recording at each core reduction step the vertex `v` and the separation `(A, B)` of `(8.2)`
together with the hypotheses of `(8.2)` (`v ∈ Z`, `¬ IsFourLinkedAt x.omega Z C v`, and
`IsMinOrderCoreSeparation x.omega Z C v A B`). -/
inductive Alg83Trace (x : Alg81Input) :
    Finset (Fin x.n) → SimpleGraph (Fin x.n) → Prop where
  | refl : Alg83Trace x Finset.univ x.G
  | step {Z : Finset (Fin x.n)} {C : SimpleGraph (Fin x.n)}
      (v : Fin x.n) (A B : Finset (Fin x.n)) :
      Alg83Trace x Z C →
      v ∈ Z →
      ¬ IsFourLinkedAt x.omega Z C v →
      IsMinOrderCoreSeparation x.omega Z C v A B →
      Alg83Trace x B (coreStepGraph C A B)

open scoped Graph in
/-- Convert a core pair `(Z, C)` (`Z : Finset (Fin n)`, `C : SimpleGraph (Fin n)`) into a
`Graph (Fin n) (Sym2 (Fin n))` by inducing `Graph.ofSimpleGraph C` on `(Z : Set (Fin n))`. -/
abbrev toCoreGraph {n : ℕ} (Z : Finset (Fin n)) (C : SimpleGraph (Fin n)) :
    Graph (Fin n) (Sym2 (Fin n)) :=
  graphOfFinsetSimpleGraph Z C

open scoped Graph in
@[simp]
theorem vertexSet_toCoreGraph {n : ℕ} (Z : Finset (Fin n)) (C : SimpleGraph (Fin n)) :
    V(toCoreGraph Z C) = (Z : Set (Fin n)) :=
  rfl

theorem isLink_toCoreGraph_iff {n : ℕ} (Z : Finset (Fin n)) (C : SimpleGraph (Fin n))
    {e : Sym2 (Fin n)} {u w : Fin n} :
    (toCoreGraph Z C).IsLink e u w ↔ (C.Adj u w ∧ e = s(u, w)) ∧ u ∈ Z ∧ w ∈ Z := by
  rw [toCoreGraph, graphOfFinsetSimpleGraph_isLink, @and_comm (e = s(u, w))]

theorem adj_toCoreGraph_iff {n : ℕ} (Z : Finset (Fin n)) (C : SimpleGraph (Fin n))
    {u w : Fin n} :
    (toCoreGraph Z C).Adj u w ↔ C.Adj u w ∧ u ∈ Z ∧ w ∈ Z :=
  graphOfFinsetSimpleGraph_adj Z C

theorem isSimpleGraph_toCoreGraph {n : ℕ} (Z : Finset (Fin n)) (C : SimpleGraph (Fin n)) :
    GM09.IsSimpleGraph (toCoreGraph Z C) :=
  isSimpleGraph_graphOfFinsetSimpleGraph Z C

open scoped Graph in
theorem toCoreGraph_univ_eq_initialCore (x : Alg81Input) :
    toCoreGraph Finset.univ x.G = GM13.initialCore x.toSociety := by
  refine Graph.ext (by simp [GM13.initialCore, GM13.coreStepGraph, Alg81Input.toSociety])
    (fun e u w => ?_)
  rw [isLink_toCoreGraph_iff]
  change ((x.G.Adj u w ∧ e = s(u, w)) ∧ u ∈ Finset.univ ∧ w ∈ Finset.univ) ↔
    (u ≠ w ∧ (x.toSociety.G.Adj u w ∨
      (u ∈ (∅ : Set (Fin x.n)) ∩ V(x.toSociety.G) ∧
       w ∈ (∅ : Set (Fin x.n)) ∩ V(x.toSociety.G))) ∧ e = s(u, w))
  rw [Alg81Input.toSociety_G]
  simp only [Finset.mem_univ, and_true, Set.empty_inter, Set.mem_empty_iff_false, and_self,
    or_false]
  have hadj_iff : (Graph.ofSimpleGraph x.G).Adj u w ↔ x.G.Adj u w := by
    constructor
    · rintro ⟨f, rfl, hf⟩
      exact x.G.mem_edgeSet.mp hf
    · intro hadj
      exact ⟨s(u, w), rfl, x.G.mem_edgeSet.mpr hadj⟩
  rw [hadj_iff]
  exact ⟨fun ⟨hadj, he⟩ => ⟨x.G.ne_of_adj hadj, hadj, he⟩, fun ⟨_, hadj, he⟩ => ⟨hadj, he⟩⟩

theorem isCoreOf_toCoreGraph_univ (x : Alg81Input) :
    GM13.IsCoreOf x.toSociety (toCoreGraph Finset.univ x.G) := by
  rw [toCoreGraph_univ_eq_initialCore]
  exact GM13.isCoreOf_initialCore x.toSociety

open scoped Graph in
/-- Left subgraph `A_G` of `toCoreGraph Z C` induced by `A : Finset (Fin n)`. -/
def coreSepLeftGraph {n : ℕ} (Z : Finset (Fin n)) (C : SimpleGraph (Fin n))
    (A : Finset (Fin n)) : Graph (Fin n) (Sym2 (Fin n)) :=
  (toCoreGraph Z C).induce (A : Set (Fin n))

open scoped Graph in
/-- Right subgraph `B_G` of `toCoreGraph Z C` induced by `B : Finset (Fin n)` with edges in
`E(A_G)` removed so `E(A_G) ∩ E(B_G) = ∅`. -/
def coreSepRightGraph {n : ℕ} (Z : Finset (Fin n)) (C : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) : Graph (Fin n) (Sym2 (Fin n)) :=
  ((toCoreGraph Z C).induce (B : Set (Fin n))).restrict
    (E(toCoreGraph Z C) \ E(coreSepLeftGraph Z C A))

open scoped Graph in
@[simp]
theorem vertexSet_coreSepLeftGraph {n : ℕ} (Z : Finset (Fin n)) (C : SimpleGraph (Fin n))
    (A : Finset (Fin n)) :
    V(coreSepLeftGraph Z C A) = (A : Set (Fin n)) :=
  rfl

open scoped Graph in
@[simp]
theorem vertexSet_coreSepRightGraph {n : ℕ} (Z : Finset (Fin n)) (C : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) :
    V(coreSepRightGraph Z C A B) = (B : Set (Fin n)) :=
  rfl

open scoped Graph in
theorem isGraphSeparation_of_isCoreSeparation {n : ℕ} {Z : Finset (Fin n)}
    {C : SimpleGraph (Fin n)} {A B : Finset (Fin n)} (hsep : IsCoreSeparation Z C A B) :
    GM06.IsGraphSeparation (toCoreGraph Z C)
      (coreSepLeftGraph Z C A) (coreSepRightGraph Z C A B) := by
  have hA_le : coreSepLeftGraph Z C A ≤ toCoreGraph Z C :=
    (toCoreGraph Z C).induce_le (Finset.coe_subset.2 hsep.1)
  have hB_le : coreSepRightGraph Z C A B ≤ toCoreGraph Z C :=
    Graph.restrict_le.trans ((toCoreGraph Z C).induce_le (Finset.coe_subset.2 hsep.2.1))
  refine ⟨hA_le, hB_le, ?_, ?_, ?_⟩
  · change (A : Set (Fin n)) ∪ (B : Set (Fin n)) = (Z : Set (Fin n))
    rw [← Finset.coe_union, hsep.2.2.1]
  · refine Set.Subset.antisymm (Set.union_subset hA_le.edgeSet_mono hB_le.edgeSet_mono)
      (fun e he => ?_)
    by_cases heA : e ∈ E(coreSepLeftGraph Z C A)
    · exact Or.inl heA
    · right
      rcases (toCoreGraph Z C).exists_isLink_of_mem_edgeSet he with ⟨u, w, hl⟩
      have hl' := (isLink_toCoreGraph_iff Z C).1 hl
      have hadj : C.Adj u w := hl'.1.1
      have huZ : u ∈ Z := hl'.2.1
      have hwZ : w ∈ Z := hl'.2.2
      have hnot_both_A : ¬ (u ∈ A ∧ w ∈ A) := by
        rintro ⟨huA, hwA⟩
        exact heA ⟨u, w, hl, huA, hwA⟩
      have huB : u ∈ B := by
        by_contra huNotB
        have huA : u ∈ A := by
          have huU : u ∈ A ∪ B := hsep.2.2.1.symm ▸ huZ
          exact (Finset.mem_union.1 huU).resolve_right huNotB
        have hwA : w ∈ A := by
          by_contra hwNotA
          have hwB : w ∈ B := by
            have hwU : w ∈ A ∪ B := hsep.2.2.1.symm ▸ hwZ
            exact (Finset.mem_union.1 hwU).resolve_left hwNotA
          exact hsep.2.2.2 u (Finset.mem_sdiff.2 ⟨huA, huNotB⟩)
            w (Finset.mem_sdiff.2 ⟨hwB, hwNotA⟩) hadj
        exact hnot_both_A ⟨huA, hwA⟩
      have hwB : w ∈ B := by
        by_contra hwNotB
        have hwA : w ∈ A := by
          have hwU : w ∈ A ∪ B := hsep.2.2.1.symm ▸ hwZ
          exact (Finset.mem_union.1 hwU).resolve_right hwNotB
        have huA : u ∈ A := by
          by_contra huNotA
          exact hsep.2.2.2 w (Finset.mem_sdiff.2 ⟨hwA, hwNotB⟩)
            u (Finset.mem_sdiff.2 ⟨huB, huNotA⟩) hadj.symm
        exact hnot_both_A ⟨huA, hwA⟩
      change e ∈ E(((toCoreGraph Z C).induce (B : Set (Fin n))).restrict
        (E(toCoreGraph Z C) \ E(coreSepLeftGraph Z C A)))
      rw [Graph.edgeSet_restrict]
      exact ⟨⟨u, w, hl, huB, hwB⟩, ⟨he, heA⟩⟩
  · change Disjoint E(coreSepLeftGraph Z C A)
      E(((toCoreGraph Z C).induce (B : Set (Fin n))).restrict
        (E(toCoreGraph Z C) \ E(coreSepLeftGraph Z C A)))
    rw [Graph.edgeSet_restrict, Set.disjoint_left]
    intro e heA heB
    exact heB.2.2 heA

open Classical in
open scoped Graph in
theorem isCoreSeparation_of_isGraphSeparation {n : ℕ} {Z : Finset (Fin n)}
    {C : SimpleGraph (Fin n)} {A' B' : Graph (Fin n) (Sym2 (Fin n))}
    (hsep : GM06.IsGraphSeparation (toCoreGraph Z C) A' B') :
    IsCoreSeparation Z C V(A').toFinset V(B').toFinset := by
  have hA_sub : V(A').toFinset ⊆ Z := by
    intro u hu
    exact hsep.1.vertexSet_mono (Set.mem_toFinset.1 hu)
  have hB_sub : V(B').toFinset ⊆ Z := by
    intro u hu
    exact hsep.2.1.vertexSet_mono (Set.mem_toFinset.1 hu)
  refine ⟨hA_sub, hB_sub, ?_, ?_⟩
  · ext u
    simp only [Finset.mem_union, Set.mem_toFinset]
    change u ∈ V(A') ∪ V(B') ↔ u ∈ Z
    rw [hsep.2.2.1]
    rfl
  · intro u hu w hw hadj
    have huA' : u ∈ V(A') \ V(B') := by
      simp only [Finset.mem_sdiff, Set.mem_toFinset] at hu
      exact hu
    have hwB' : w ∈ V(B') \ V(A') := by
      simp only [Finset.mem_sdiff, Set.mem_toFinset] at hw
      exact hw
    have hadj_core : (toCoreGraph Z C).Adj u w :=
      (adj_toCoreGraph_iff Z C).2 ⟨hadj, hA_sub (Finset.mem_sdiff.1 hu).1,
        hB_sub (Finset.mem_sdiff.1 hw).1⟩
    exact GM13.not_adj_of_isGraphSeparation hsep huA' hwB' hadj_core

open scoped Graph in
theorem ncard_inter_coreSepGraphs {n : ℕ} (Z : Finset (Fin n)) (C : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) :
    (V(coreSepLeftGraph Z C A) ∩ V(coreSepRightGraph Z C A B)).ncard = (A ∩ B).card := by
  change ((A : Set (Fin n)) ∩ (B : Set (Fin n))).ncard = (A ∩ B).card
  rw [← Finset.coe_inter, Set.ncard_coe_finset]

open Classical in
open scoped Graph in
theorem card_inter_toFinset_of_isGraphSeparation {n : ℕ}
    (A' B' : Graph (Fin n) (Sym2 (Fin n))) :
    (V(A').toFinset ∩ V(B').toFinset).card = (V(A') ∩ V(B')).ncard := by
  rw [← Set.ncard_coe_finset, Finset.coe_inter, Set.coe_toFinset, Set.coe_toFinset]

open Classical in
open scoped Graph in
theorem isFourLinkedAt_iff_isFourLinkedVertexIn (x : Alg81Input) {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} {v : Fin x.n} (hv : v ∈ Z) :
    IsFourLinkedAt x.omega Z C v ↔
      GM13.IsFourLinkedVertexIn x.toSociety (toCoreGraph Z C) v := by
  constructor
  · intro h4
    refine ⟨hv, fun A' B' hsep' hord' hbar' hv' => ?_⟩
    have hcore_sep := isCoreSeparation_of_isGraphSeparation hsep'
    have hcard : (V(A').toFinset ∩ V(B').toFinset).card ≤ 3 := by
      rw [card_inter_toFinset_of_isGraphSeparation]
      exact hord'
    have homega : x.omega.toFinset ⊆ V(B').toFinset := by
      intro u hu
      rw [Set.mem_toFinset]
      exact hbar' (by rw [Alg81Input.toSociety_bar]; exact List.mem_toFinset.1 hu)
    have hv_in : v ∈ V(A').toFinset \ V(B').toFinset := by
      simp only [Finset.mem_sdiff, Set.mem_toFinset]
      exact hv'
    exact h4 V(A').toFinset V(B').toFinset hcore_sep hcard homega hv_in
  · intro h4 A B hsep hcard homega hv_AB
    have hgraph_sep := isGraphSeparation_of_isCoreSeparation hsep
    have hord : (V(coreSepLeftGraph Z C A) ∩ V(coreSepRightGraph Z C A B)).ncard ≤ 3 := by
      rw [ncard_inter_coreSepGraphs]
      exact hcard
    have hbar : x.toSociety.Ω.bar ⊆ V(coreSepRightGraph Z C A B) := by
      intro u hu
      rw [Alg81Input.toSociety_bar] at hu
      exact homega (List.mem_toFinset.2 hu)
    have hv' : v ∈ V(coreSepLeftGraph Z C A) \ V(coreSepRightGraph Z C A B) := by
      simpa using hv_AB
    exact h4.2 (coreSepLeftGraph Z C A) (coreSepRightGraph Z C A B) hgraph_sep hord hbar hv'

open scoped Graph in
theorem adj_coreSepRightGraph_iff {n : ℕ} {Z : Finset (Fin n)} {C : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} (hsep : IsCoreSeparation Z C A B) {u w : Fin n} :
    (coreSepRightGraph Z C A B).Adj u w ↔
      u ∈ B ∧ w ∈ B ∧ C.Adj u w ∧ ¬ (u ∈ A ∧ w ∈ A) := by
  constructor
  · rintro ⟨e, hl⟩
    have hl_le : coreSepRightGraph Z C A B ≤ (toCoreGraph Z C).induce (B : Set (Fin n)) :=
      Graph.restrict_le
    have he_mem : e ∈ E(coreSepRightGraph Z C A B) := hl.edge_mem
    have hl_ind : ((toCoreGraph Z C).induce (B : Set (Fin n))).IsLink e u w :=
      hl.mono hl_le
    rw [Graph.induce_isLink, isLink_toCoreGraph_iff] at hl_ind
    change e ∈ E(((toCoreGraph Z C).induce (B : Set (Fin n))).restrict
      (E(toCoreGraph Z C) \ E(coreSepLeftGraph Z C A))) at he_mem
    rw [Graph.edgeSet_restrict] at he_mem
    have he_not_A : e ∉ E(coreSepLeftGraph Z C A) := he_mem.2.2
    refine ⟨hl_ind.2.1, hl_ind.2.2, hl_ind.1.1.1, ?_⟩
    rintro ⟨huA, hwA⟩
    exact he_not_A ⟨u, w, (isLink_toCoreGraph_iff Z C).2 hl_ind.1, huA, hwA⟩
  · rintro ⟨huB, hwB, hadj, hnotA⟩
    have huZ : u ∈ Z := hsep.2.1 huB
    have hwZ : w ∈ Z := hsep.2.1 hwB
    have hl_core : (toCoreGraph Z C).IsLink s(u, w) u w :=
      (isLink_toCoreGraph_iff Z C).2 ⟨⟨hadj, rfl⟩, huZ, hwZ⟩
    have hl_ind : ((toCoreGraph Z C).induce (B : Set (Fin n))).IsLink s(u, w) u w := by
      rw [Graph.induce_isLink]
      exact ⟨hl_core, huB, hwB⟩
    have he_not_A : s(u, w) ∉ E(coreSepLeftGraph Z C A) := by
      rintro ⟨x, y, hl_xy, hxA, hyA⟩
      have hl_xy' := (isLink_toCoreGraph_iff Z C).1 hl_xy
      rcases Sym2.eq_iff.1 hl_xy'.1.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnotA ⟨hxA, hyA⟩
      · exact hnotA ⟨hyA, hxA⟩
    have he_right : s(u, w) ∈ E(coreSepRightGraph Z C A B) := by
      change s(u, w) ∈ E(((toCoreGraph Z C).induce (B : Set (Fin n))).restrict
        (E(toCoreGraph Z C) \ E(coreSepLeftGraph Z C A)))
      rw [Graph.edgeSet_restrict]
      exact ⟨hl_ind.edge_mem, ⟨hl_core.edge_mem, he_not_A⟩⟩
    exact ⟨s(u, w), (Graph.restrict_le.isLink_iff he_right).2 hl_ind⟩

open scoped Graph in
theorem isCoreStepGraph_toCoreGraph {n : ℕ} {Z : Finset (Fin n)} {C : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} (hsep : IsCoreSeparation Z C A B) :
    GM13.IsCoreStepGraph (coreSepRightGraph Z C A B)
      (V(coreSepLeftGraph Z C A) ∩ V(coreSepRightGraph Z C A B))
      (toCoreGraph B (coreStepGraph C A B)) where
  isSimple := isSimpleGraph_toCoreGraph B (coreStepGraph C A B)
  finite_E := Set.toFinite _
  vertexSet_eq := rfl
  adj_iff u w := by
    rw [adj_toCoreGraph_iff, adj_coreSepRightGraph_iff hsep]
    simp only [coreStepGraph, vertexSet_coreSepLeftGraph, vertexSet_coreSepRightGraph,
      Set.mem_inter_iff, Finset.mem_coe, Finset.mem_inter]
    constructor
    · rintro ⟨⟨huB, hwB, hne, hadj | ⟨⟨huA, _⟩, ⟨hwA, _⟩⟩⟩, _, _⟩
      · by_cases hboth : u ∈ A ∧ w ∈ A
        · exact Or.inr ⟨⟨⟨hboth.1, huB⟩, huB⟩, ⟨⟨hboth.2, hwB⟩, hwB⟩, hne⟩
        · exact Or.inl ⟨huB, hwB, hadj, hboth⟩
      · exact Or.inr ⟨⟨⟨huA, huB⟩, huB⟩, ⟨⟨hwA, hwB⟩, hwB⟩, hne⟩
    · rintro (⟨huB, hwB, hadj, _⟩ | ⟨⟨⟨huA, huB⟩, _⟩, ⟨⟨hwA, hwB⟩, _⟩, hne⟩)
      · exact ⟨⟨huB, hwB, C.ne_of_adj hadj, Or.inl hadj⟩, huB, hwB⟩
      · exact ⟨⟨huB, hwB, hne, Or.inr ⟨⟨huA, huB⟩, ⟨hwA, hwB⟩⟩⟩, huB, hwB⟩

open Classical in
open scoped Graph in
/-- Every pair `(Z, C)` reachable by `Alg83Trace x Z C` is a core of `x.toSociety` in the sense of
`GM13.IsCoreOf`, proved by induction on `Alg83Trace` using `GM13.isCoreOf_initialCore` and
`GM13.theorem_8_2_proof` one step at a time as in the paper's description of `(8.3)` (page 95). -/
theorem Alg83Trace.isCoreOf {x : Alg81Input} {Z : Finset (Fin x.n)} {C : SimpleGraph (Fin x.n)}
    (htrace : Alg83Trace x Z C) :
    GM13.IsCoreOf x.toSociety (toCoreGraph Z C) := by
  induction htrace with
  | refl =>
    exact isCoreOf_toCoreGraph_univ x
  | @step Z C v A B _ hvZ hnot4 hmin ih =>
    have hv_not_4 : ¬ GM13.IsFourLinkedVertexIn x.toSociety (toCoreGraph Z C) v :=
      fun h => hnot4 ((isFourLinkedAt_iff_isFourLinkedVertexIn x hvZ).2 h)
    have hsep := isGraphSeparation_of_isCoreSeparation hmin.1
    have hv_AB : v ∈ V(coreSepLeftGraph Z C A) \ V(coreSepRightGraph Z C A B) := by
      simpa using hmin.2.1
    have hbar : x.toSociety.Ω.bar ⊆ V(coreSepRightGraph Z C A B) := by
      intro u hu
      rw [Alg81Input.toSociety_bar] at hu
      exact hmin.2.2.1 (List.mem_toFinset.2 hu)
    have hmin_G : ∀ A' B' : Graph (Fin x.n) (Sym2 (Fin x.n)),
        GM06.IsGraphSeparation (toCoreGraph Z C) A' B' →
        v ∈ V(A') \ V(B') → x.toSociety.Ω.bar ⊆ V(B') →
        (V(coreSepLeftGraph Z C A) ∩ V(coreSepRightGraph Z C A B)).ncard ≤
          (V(A') ∩ V(B')).ncard := by
      intro A' B' hsep' hv' hbar'
      rw [ncard_inter_coreSepGraphs, ← card_inter_toFinset_of_isGraphSeparation]
      refine hmin.2.2.2.2 V(A').toFinset V(B').toFinset
        (isCoreSeparation_of_isGraphSeparation hsep') ?_ ?_
      · simp only [Finset.mem_sdiff, Set.mem_toFinset]
        exact hv'
      · intro u hu
        rw [Set.mem_toFinset]
        exact hbar' (by rw [Alg81Input.toSociety_bar]; exact List.mem_toFinset.1 hu)
    have hstep := isCoreStepGraph_toCoreGraph hmin.1
    exact (GM13.theorem_8_2_proof ih hvZ hv_not_4 hsep hv_AB hbar hmin_G hstep).1

/-- When `Alg83Trace x Z C` and `IsFourLinkedCore x.omega Z C` both hold, `toCoreGraph Z C` is a
4-linked core of `x.toSociety` in the sense of `GM13.IsFourLinkedCore`. -/
theorem isFourLinkedCore_toCoreGraph {x : Alg81Input} {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C)
    (h4 : IsFourLinkedCore x.omega Z C) :
    GM13.IsFourLinkedCore x.toSociety (toCoreGraph Z C) where
  isCore := htrace.isCoreOf
  fourLinked v hv := (isFourLinkedAt_iff_isFourLinkedVertexIn x hv).1 (h4.2.2 v hv)

/-! ## Section 2: Word RAM Subroutines for Bitsets and Core Step Graph Updates -/

/-- Build a singleton bitset `IsBitSet {v} a_X` in `O(n)` steps by allocating `a_X` of size
`r_n` (`n`) and writing `1` at `r_v` (`v.1`). -/
def alg83SingletonProg (a_X : Arr) (r_n r_v : Reg) : Cmd :=
  .seq (.alloc a_X (.reg r_n))
    (.write a_X (.reg r_v) (.const 1))

theorem alg83SingletonProg_exec {w n : ℕ} (v : Fin n) (a_X : Arr) (r_n r_v : Reg)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hrn : s.regs r_n = n) (hrv : s.regs r_v = v.1) :
    ∃ s' t,
      Exec w (alg83SingletonProg a_X r_n r_v) s s' t ∧
      t ≤ n + 4 ∧
      IsBitSet ({v} : Finset (Fin n)) a_X s' ∧
      (∀ a : Arr, a ≠ a_X → s'.arrs a = s.arrs a) ∧
      s'.regs = s.regs := by
  have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
  let s₁ := s.setArr a_X (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_X (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.writeArr a_X v.1 1
  have hex₂ : Exec w (.write a_X (.reg r_v) (.const 1)) s₁ s₂ 3 :=
    .write (by simp [s₁, Expr.eval, checkWord, hrv, hv_w])
      (by simp [Expr.eval, checkWord, hw])
      (by simp [s₁, v.2])
  have hbit : IsBitSet ({v} : Finset (Fin n)) a_X s₂ := by
    refine ⟨by simp [s₂, s₁], fun u => ?_, fun u => ?_⟩
    · simp only [s₂, s₁, State.writeArr, State.setArr, Function.update_self,
        List.getElem_set, List.getElem_replicate]
      split_ifs <;> omega
    · simp only [s₂, s₁, State.writeArr, State.setArr, Function.update_self,
        List.getElem_set, List.getElem_replicate, Finset.mem_singleton, Fin.ext_iff]
      split_ifs with h
      · exact ⟨fun _ => h.symm, fun _ => by omega⟩
      · exact ⟨fun h0 => absurd rfl h0, fun hv_eq => absurd hv_eq.symm h⟩
  refine ⟨s₂, (1 + n) + 3, .seq hex₁ hex₂, by omega, hbit, ?_, rfl⟩
  intro a ha
  simp [s₂, s₁, State.writeArr, State.setArr, ha]

/-- Initialize `a_Z` to `IsBitSet Finset.univ a_Z` of length `n = r_14` using scratch register `2`. -/
def alg83InitUnivProg (a_Z : Arr) : Cmd :=
  .seq (.alloc a_Z (.reg 14))
    (.seq (.assign 2 (.const 0))
      (forUp 2 (.reg 14) (.write a_Z (.reg 2) (.const 1))))

theorem alg83InitUnivLoop_exec {w n : ℕ} (a_Z : Arr)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hrn : s.regs 14 = n) (hru : s.regs 2 = k)
    (harr : s.arrs a_Z = (bitSetList (Finset.univ : Finset (Fin n))).take k ++ List.replicate (n - k) 0) :
    ∃ s' t,
      Exec w (forUp 2 (.reg 14) (.write a_Z (.reg 2) (.const 1))) s s' t ∧
      t ≤ 3 + 10 * rem ∧
      IsBitSet (Finset.univ : Finset (Fin n)) a_Z s' ∧
      (∀ a : Arr, a ≠ a_Z → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hru harr
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hn_w]
    have htake : (bitSetList (Finset.univ : Finset (Fin n))).take n =
        bitSetList (Finset.univ : Finset (Fin n)) :=
      List.take_of_length_le (by simp)
    rw [htake, Nat.sub_self, List.replicate_zero, List.append_nil] at harr
    exact ⟨s, 3, .while_false hcond, by omega,
      IsBitSet.of_bitSetList _ _ _ harr, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hk_w, hn_w, hk_lt, hw]
    have hlen : (s.arrs a_Z).length = n := by
      rw [harr, List.length_append, List.length_take, length_bitSetList, List.length_replicate]; omega
    let s₁ := s.writeArr a_Z k 1
    have hex₁ : Exec w (.write a_Z (.reg 2) (.const 1)) s s₁ 3 :=
      .write (by simp [Expr.eval, checkWord, hru, hk_w])
        (by simp [Expr.eval, checkWord, hw])
        (by rw [hlen]; exact hk_lt)
    let s₂ := s₁.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₁ s₂ 4 :=
      .assign (by
        simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have harr₂ : s₂.arrs a_Z =
        (bitSetList (Finset.univ : Finset (Fin n))).take (k + 1) ++
          List.replicate (n - (k + 1)) 0 := by
      have hset : s₂.arrs a_Z = (s.arrs a_Z).set k 1 := by simp [s₂, s₁]
      rw [hset, harr]
      have hlen_take : ((bitSetList (Finset.univ : Finset (Fin n))).take k).length = k := by
        rw [List.length_take, length_bitSetList]; omega
      rw [List.set_append_right _ _ (by omega)]
      have hsub0 : k - ((bitSetList (Finset.univ : Finset (Fin n))).take k).length = 0 := by omega
      have hrep : n - k = (n - (k + 1)) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      have hbit_len : k < (bitSetList (Finset.univ : Finset (Fin n))).length := by simp [hk_lt]
      rw [take_add_one_eq_append_getElem _ k hbit_len,
        getElem_bitSetList (Finset.univ : Finset (Fin n)) k hk_lt]
      simp [List.append_assoc]
    rcases ih (k + 1) (by omega) (by simp [s₂, s₁, State.setReg, hrn])
        (by simp [s₂]) harr₂ with
      ⟨s₃, t₃, hex₃, ht₃, hbit₃, harr₃, hreg₃⟩
    refine ⟨s₃, 3 + (3 + 4) + t₃, .while_true hcond (by omega) (.seq hex₁ hex_inc) hex₃,
      by omega, hbit₃,
      fun a ha => by rw [harr₃ a ha]; simp [s₂, s₁, ha],
      fun r hr => by rw [hreg₃ r hr]; simp [s₂, s₁, State.setReg, hr]⟩

theorem alg83InitUnivProg_exec {w n : ℕ} (a_Z : Arr)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hrn : s.regs 14 = n) :
    ∃ s' t,
      Exec w (alg83InitUnivProg a_Z) s s' t ∧
      t ≤ 11 * n + 6 ∧
      IsBitSet (Finset.univ : Finset (Fin n)) a_Z s' ∧
      (∀ a : Arr, a ≠ a_Z → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_Z (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_Z (.reg 14)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg 2 0
  have hex₂ : Exec w (.assign 2 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases alg83InitUnivLoop_exec a_Z hw hn_w n 0 (by omega) (s := s₂)
      hrn rfl (by simp [s₂, s₁]) with
    ⟨s₃, t₃, hex₃, ht₃, hbit₃, harr₃, hreg₃⟩
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hbit₃,
    fun a ha => by rw [harr₃ a ha]; simp [s₂, s₁, ha],
    fun r hr => by rw [hreg₃ r hr]; simp [s₂, s₁, State.setReg, hr]⟩

/-- Update `a_Z = 14` in place from `IsBitSet Z 14` to `IsBitSet (Z ∩ VA) 14`, where
`a_VA = 12` holds `IsBitSet VA 12` and `r_14 = n`. -/
def updateZBody : Cmd :=
  .seq (.assign 3 (.read 12 (.reg 2)))
    (.ite (.reg 3) .skip (.write 14 (.reg 2) (.const 0)))

def updateZProg : Cmd :=
  .seq (.assign 2 (.const 0))
    (forUp 2 (.reg 14) updateZBody)

theorem updateZLoop_exec {w n : ℕ} (Z VA : Finset (Fin n))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hVA : IsBitSet VA 12 s)
    (hrn : s.regs 14 = n) (hru : s.regs 2 = k)
    (hZ_arr : s.arrs 14 = (bitSetList (Z ∩ VA)).take k ++ (bitSetList Z).drop k) :
    ∃ s' t,
      Exec w (forUp 2 (.reg 14) updateZBody) s s' t ∧
      t ≤ 3 + 15 * rem ∧
      IsBitSet (Z ∩ VA) 14 s' ∧
      (∀ a : Arr, a ≠ 14 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hru hZ_arr
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hn_w]
    have htake : (bitSetList (Z ∩ VA)).take n = bitSetList (Z ∩ VA) :=
      List.take_of_length_le (by simp)
    have hdrop : (bitSetList Z).drop n = [] :=
      List.drop_of_length_le (by simp)
    rw [htake, hdrop, List.append_nil] at hZ_arr
    exact ⟨s, 3, .while_false hcond, by omega,
      IsBitSet.of_bitSetList _ _ _ hZ_arr, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let uk : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hk_w, hn_w, hk_lt, hw]
    have hk_VA : k < (s.arrs 12).length := by rw [hVA.1]; exact hk_lt
    let vA := (s.arrs 12)[k]'hk_VA
    have hvA_le : vA ≤ 1 := hVA.2.1 uk
    have hvA_w : vA < 2 ^ w := by omega
    let s₁ := s.setReg 3 vA
    have hex₁ : Exec w (.assign 3 (.read 12 (.reg 2))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hk_w, hk_VA, vA, hvA_w])
    have hZ_len : (s.arrs 14).length = n := by
      rw [hZ_arr, List.length_append, List.length_take, List.length_drop,
        length_bitSetList, length_bitSetList]
      omega
    have hdrop_split : (bitSetList Z).drop k =
        [(bitSetList Z)[k]'(by simp [hk_lt])] ++ (bitSetList Z).drop (k + 1) :=
      List.drop_eq_getElem_cons (by simp [hk_lt])
    have hstep : ∃ s₂ t_b,
        Exec w (.ite (.reg 3) .skip (.write 14 (.reg 2) (.const 0))) s₁ s₂ t_b ∧
        t_b ≤ 4 ∧
        s₂.arrs 14 = (bitSetList (Z ∩ VA)).take (k + 1) ++ (bitSetList Z).drop (k + 1) ∧
        (∀ a : Arr, a ≠ 14 → s₂.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ 3 → s₂.regs r = s.regs r) := by
      by_cases hvA_ne : vA ≠ 0
      · have huk_VA : uk ∈ VA := (hVA.2.2 uk).mp hvA_ne
        have hcond3 : (Expr.reg 3).eval w s₁ = some vA := by
          simp [s₁, State.setReg, Expr.eval, checkWord, hvA_w]
        have hbit_eq : (bitSetList Z)[k]'(by simp [hk_lt]) =
            (bitSetList (Z ∩ VA))[k]'(by simp [hk_lt]) := by
          rw [getElem_bitSetList Z k hk_lt, getElem_bitSetList (Z ∩ VA) k hk_lt]
          simp [uk, huk_VA]
        have harr_eq : s₁.arrs 14 =
            (bitSetList (Z ∩ VA)).take (k + 1) ++ (bitSetList Z).drop (k + 1) := by
          change s.arrs 14 = _
          rw [hZ_arr, hdrop_split, hbit_eq, ← List.append_assoc,
            ← take_add_one_eq_append_getElem (bitSetList (Z ∩ VA)) k (by simp [hk_lt])]
        exact ⟨s₁, 1 + 1, .ite_true hcond3 hvA_ne (.skip s₁), by omega, harr_eq,
          fun _ _ => rfl, fun r h3 => by simp [s₁, State.setReg, h3]⟩
      · have hvA0 : vA = 0 := by omega
        have huk_notVA : uk ∉ VA := fun h => hvA_ne ((hVA.2.2 uk).mpr h)
        have hcond3 : (Expr.reg 3).eval w s₁ = some 0 := by
          simp [s₁, State.setReg, Expr.eval, checkWord, hvA0, h0_w]
        let s₂ := s₁.writeArr 14 k 0
        have hex_w : Exec w (.write 14 (.reg 2) (.const 0)) s₁ s₂ 3 :=
          .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hru, hk_w])
            (by simp [Expr.eval, checkWord, h0_w])
            (by simp [s₁, hZ_len, hk_lt])
        have harr_eq : s₂.arrs 14 =
            (bitSetList (Z ∩ VA)).take (k + 1) ++ (bitSetList Z).drop (k + 1) := by
          have hset : s₂.arrs 14 = (s.arrs 14).set k 0 := by simp [s₂, s₁]
          rw [hset, hZ_arr, hdrop_split]
          have hlen_take : ((bitSetList (Z ∩ VA)).take k).length = k := by
            rw [List.length_take, length_bitSetList]; omega
          rw [List.set_append_right _ _ (by omega)]
          have hsub0 : k - ((bitSetList (Z ∩ VA)).take k).length = 0 := by omega
          rw [hsub0, List.singleton_append, List.set_cons_zero]
          have hbit0 : (bitSetList (Z ∩ VA))[k]'(by simp [hk_lt]) = 0 := by
            rw [getElem_bitSetList (Z ∩ VA) k hk_lt]
            simp [uk, huk_notVA]
          rw [← hbit0, ← List.singleton_append, ← List.append_assoc,
            ← take_add_one_eq_append_getElem (bitSetList (Z ∩ VA)) k (by simp [hk_lt])]
        exact ⟨s₂, 1 + 3, .ite_false hcond3 hex_w, by omega, harr_eq,
          fun a ha => by simp [s₂, s₁, ha],
          fun r h3 => by simp [s₂, s₁, State.setReg, h3]⟩
    rcases hstep with ⟨s₂, t_b, hex_b, ht_b, hZ_arr₂, harr₂, hreg₂⟩
    let s₃ := s₂.setReg 2 (k + 1)
    have hr2_s₂ : s₂.regs 2 = k := by
      rw [hreg₂ 2 (by decide), hru]
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₂ s₃ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_s₂, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    rcases ih (k + 1) (by omega) (s := s₃)
        (hVA.of_arr_eq (by simp [s₃, harr₂ 12 (by decide)]))
        (by simp [s₃, State.setReg, hreg₂ 14 (by decide), hrn])
        (by simp [s₃]) (by simpa [s₃] using hZ_arr₂) with
      ⟨s₄, t₄, hex₄, ht₄, hZ_bit₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + t_b) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex_b) hex_inc) hex₄,
      by omega, hZ_bit₄,
      fun a ha => by rw [harr₄ a ha]; exact harr₂ a ha,
      fun r h2 h3 => by
        rw [hreg₄ r h2 h3]
        simp [s₃, State.setReg, h2, hreg₂ r h3]⟩

lemma isBitSet_eq_bitSetList {n : ℕ} {S : Finset (Fin n)} {a : Arr} {s : State}
    (h : IsBitSet S a s) : s.arrs a = bitSetList S := by
  refine List.ext_getElem (by rw [h.1, length_bitSetList]) fun i h1 h2 => ?_
  have hi : i < n := by rw [← h.1]; exact h1
  rw [h.getElem_eq_ite ⟨i, hi⟩, getElem_bitSetList]

theorem updateZProg_exec {w n : ℕ} (Z VA : Finset (Fin n))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hZ : IsBitSet Z 14 s) (hVA : IsBitSet VA 12 s)
    (hrn : s.regs 14 = n) :
    ∃ s' t,
      Exec w updateZProg s s' t ∧
      t ≤ 15 * n + 5 ∧
      IsBitSet (Z ∩ VA) 14 s' ∧
      (∀ a : Arr, a ≠ 14 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 2 0
  have hex₁ : Exec w (.assign 2 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hZ_arr₁ : s₁.arrs 14 = (bitSetList (Z ∩ VA)).take 0 ++ (bitSetList Z).drop 0 := by
    simp [s₁, isBitSet_eq_bitSetList hZ]
  have hrn₁ : s₁.regs 14 = n := by simp [s₁, State.setReg, hrn]
  have hru₁ : s₁.regs 2 = 0 := by simp [s₁]
  rcases updateZLoop_exec Z VA hw hn_w n 0 (by omega) (s := s₁) (hVA.of_arr_eq rfl) hrn₁ hru₁ hZ_arr₁ with
    ⟨s₂, t₂, hex₂, ht₂, hbit₂, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hbit₂, harr₂,
    fun r h2 h3 => by rw [hreg₂ r h2 h3]; simp [s₁, State.setReg, h2]⟩

/-- Collect the vertices of `A ∩ B` (`u ∈ B ∧ u ∈ VB`, where `B` is in `a_Z = 14` and `VB` is in
`a_VB = 13`, since `A = Z ∩ VB` and `B = Z ∩ VA`) in increasing order into `a_K = 16` with count
in `r_21`. -/
def collectKBody : Cmd :=
  .seq (.assign 3 (.read 14 (.reg 2)))
    (.seq (.assign 4 (.read 13 (.reg 2)))
      (.ite (.op .mul (.reg 3) (.reg 4))
        (.seq (.write 16 (.reg 21) (.reg 2))
          (.assign 21 (.op .add (.reg 21) (.const 1))))
        .skip))

def collectKProg : Cmd :=
  .seq (.alloc 16 (.reg 14))
    (.seq (.assign 21 (.const 0))
      (.seq (.assign 2 (.const 0))
        (forUp 2 (.reg 14) collectKBody)))

theorem collectKLoop_exec {w n : ℕ} (A B VB : Finset (Fin n))
    (hAB_iff : ∀ u : Fin n, u ∈ A ∩ B ↔ u ∈ B ∧ u ∈ VB)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hB : IsBitSet B 14 s) (hVB : IsBitSet VB 13 s)
    (hrn : s.regs 14 = n) (hru : s.regs 2 = k)
    (hr21 : s.regs 21 = (((List.finRange n).take k).filter (· ∈ A ∩ B)).length)
    (hK_len : (s.arrs 16).length = n)
    (hK_get : ∀ i (hi : i < (((List.finRange n).take k).filter (· ∈ A ∩ B)).length),
      (s.arrs 16).getD i 0 = ((((List.finRange n).take k).filter (· ∈ A ∩ B))[i]'hi).1) :
    ∃ s' t,
      Exec w (forUp 2 (.reg 14) collectKBody) s s' t ∧
      t ≤ 3 + 23 * rem ∧
      s'.regs 21 = ((List.finRange n).filter (· ∈ A ∩ B)).length ∧
      (s'.arrs 16).length = n ∧
      (∀ i (hi : i < ((List.finRange n).filter (· ∈ A ∩ B)).length),
        (s'.arrs 16).getD i 0 = (((List.finRange n).filter (· ∈ A ∩ B))[i]'hi).1) ∧
      (∀ a : Arr, a ≠ 16 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 21 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hru hr21 hK_get
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hn_w]
    have htake : (List.finRange n).take n = List.finRange n :=
      List.take_of_length_le (by simp)
    rw [htake] at hr21 hK_get
    exact ⟨s, 3, .while_false hcond, by omega, hr21, hK_len, hK_get,
      fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let uk : Fin n := ⟨k, hk_lt⟩
    let K_k := ((List.finRange n).take k).filter (· ∈ A ∩ B)
    let K_next := ((List.finRange n).take (k + 1)).filter (· ∈ A ∩ B)
    have hK_k_le : K_k.length ≤ k := by
      calc
        K_k.length ≤ ((List.finRange n).take k).length := List.length_filter_le _ _
        _ = k := by rw [List.length_take, List.length_finRange]; omega
    have htake_succ : (List.finRange n).take (k + 1) = (List.finRange n).take k ++ [uk] := by
      have hlen_fr : k < (List.finRange n).length := by simp [hk_lt]
      rw [take_add_one_eq_append_getElem (List.finRange n) k hlen_fr]
      simp [uk]
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hk_w, hn_w, hk_lt, hw]
    have hk_B : k < (s.arrs 14).length := by rw [hB.1]; exact hk_lt
    let vB := (s.arrs 14)[k]'hk_B
    have hvB_eq : vB = if uk ∈ B then 1 else 0 := hB.getElem_eq_ite uk
    have hvB_w : vB < 2 ^ w := by rw [hvB_eq]; split_ifs <;> omega
    let s₁ := s.setReg 3 vB
    have hex₁ : Exec w (.assign 3 (.read 14 (.reg 2))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hk_w, hk_B, vB, hvB_w])
    have hk_VB : k < (s.arrs 13).length := by rw [hVB.1]; exact hk_lt
    let vVB := (s.arrs 13)[k]'hk_VB
    have hvVB_eq : vVB = if uk ∈ VB then 1 else 0 := hVB.getElem_eq_ite uk
    have hvVB_w : vVB < 2 ^ w := by rw [hvVB_eq]; split_ifs <;> omega
    let s₂ := s₁.setReg 4 vVB
    have hex₂ : Exec w (.assign 4 (.read 13 (.reg 2))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hru, hk_w, hk_VB, vVB, hvVB_w])
    have hstep : ∃ s₃ t_b,
        Exec w (.ite (.op .mul (.reg 3) (.reg 4))
          (.seq (.write 16 (.reg 21) (.reg 2))
            (.assign 21 (.op .add (.reg 21) (.const 1))))
          .skip) s₂ s₃ t_b ∧
        t_b ≤ 10 ∧
        s₃.regs 2 = k ∧
        s₃.regs 21 = K_next.length ∧
        (s₃.arrs 16).length = n ∧
        (∀ i (hi : i < K_next.length), (s₃.arrs 16).getD i 0 = (K_next[i]'hi).1) ∧
        (∀ a : Arr, a ≠ 16 → s₃.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 21 → s₃.regs r = s.regs r) := by
      by_cases huk_AB : uk ∈ A ∩ B
      · have huk_B : uk ∈ B := ((hAB_iff uk).mp huk_AB).1
        have huk_VB : uk ∈ VB := ((hAB_iff uk).mp huk_AB).2
        have hvB1 : vB = 1 := by simp [hvB_eq, huk_B]
        have hvVB1 : vVB = 1 := by simp [hvVB_eq, huk_VB]
        have hcond_mul : (Expr.op .mul (.reg 3) (.reg 4)).eval w s₂ = some 1 := by
          simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hvB1, hvVB1, hw]
        have hK_next_eq : K_next = K_k ++ [uk] := by
          dsimp [K_next, K_k]
          rw [htake_succ, List.filter_append, List.filter_cons_of_pos (by simp [huk_AB]),
            List.filter_nil]
        have hr21_lt : K_k.length < n := by omega
        have hr21_w : K_k.length < 2 ^ w := by omega
        have hr21_s₂ : s₂.regs 21 = K_k.length := hr21
        let s₂a := s₂.writeArr 16 K_k.length k
        have hex_w : Exec w (.write 16 (.reg 21) (.reg 2)) s₂ s₂a 3 :=
          .write (by simp [Expr.eval, checkWord, hr21_s₂, hr21_w])
            (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hru, hk_w])
            (by simp [s₂, s₁, hK_len, hr21_lt])
        let s₃ := s₂a.setReg 21 (K_k.length + 1)
        have hr21_s₂a : s₂a.regs 21 = K_k.length := hr21
        have hex_inc21 : Exec w (.assign 21 (.op .add (.reg 21) (.const 1))) s₂a s₃ 4 :=
          .assign (by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr21_s₂a, hr21_w, hw, show K_k.length + 1 < 2 ^ w by omega])
        refine ⟨s₃, 3 + (3 + 4), .ite_true hcond_mul (by decide) (.seq hex_w hex_inc21),
          by omega, hru, ?_, by simp [s₃, s₂a, s₂, s₁, hK_len], ?_,
          fun a ha => by simp [s₃, s₂a, s₂, s₁, ha],
          fun r _ h3 h4 h21 => by simp [s₃, s₂a, s₂, s₁, State.setReg, h3, h4, h21]⟩
        · simp [s₃, hK_next_eq]
        · intro i hi
          have hi' : i < K_k.length + 1 := by rw [hK_next_eq, List.length_append] at hi; simpa using hi
          have hi_arr : i < (s.arrs 16).length := by omega
          change ((s.arrs 16).set K_k.length k)[i]?.getD 0 = (K_next[i]'hi).1
          rw [List.getElem?_eq_getElem (by simp [hi_arr]), Option.getD_some]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi_lt | rfl
          · rw [List.getElem_set_ne (by omega)]
            have hget := hK_get i hi_lt
            change (s.arrs 16)[i]?.getD 0 = _ at hget
            rw [List.getElem?_eq_getElem hi_arr, Option.getD_some] at hget
            simp only [hK_next_eq, List.getElem_append_left hi_lt]
            exact hget
          · rw [List.getElem_set_self]
            simp [hK_next_eq, uk]
      · have hnot_both : ¬(uk ∈ B ∧ uk ∈ VB) := fun h => huk_AB ((hAB_iff uk).mpr h)
        have hmul0 : vB * vVB = 0 := by
          rw [hvB_eq, hvVB_eq]
          by_cases h1 : uk ∈ B <;> by_cases h2 : uk ∈ VB
          · exfalso; exact hnot_both ⟨h1, h2⟩
          · simp [h1, h2]
          · simp [h1, h2]
          · simp [h1, h2]
        have hcond_mul : (Expr.op .mul (.reg 3) (.reg 4)).eval w s₂ = some 0 := by
          simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hvB_w, hvVB_w, hmul0, h0_w]
        have hK_next_eq : K_next = K_k := by
          dsimp [K_next, K_k]
          rw [htake_succ, List.filter_append, List.filter_cons_of_neg (by simp [huk_AB]),
            List.filter_nil, List.append_nil]
        refine ⟨s₂, 3 + 1, .ite_false hcond_mul (.skip s₂), by omega, hru,
          by simp [s₂, s₁, State.setReg, hK_next_eq, hr21, K_k],
          by simp [s₂, s₁, hK_len],
          fun i hi => ?_,
          fun _ _ => rfl,
          fun r _ h3 h4 _ => by simp [s₂, s₁, State.setReg, h3, h4]⟩
        have hi' : i < K_k.length := by rwa [← hK_next_eq]
        have hget := hK_get i hi'
        simp only [hK_next_eq]
        exact hget
    rcases hstep with ⟨s₃, t_b, hex_b, ht_b, hr2_s₃, hr21₃, hK_len₃, hK_get₃, harr₃, hreg₃⟩
    let s₄ := s₃.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_s₃, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have hr21₄ : s₄.regs 21 = K_next.length := hr21₃
    rcases ih (k + 1) (by omega)
        (hB.of_arr_eq (by simp [s₄, harr₃ 14 (by decide)]))
        (hVB.of_arr_eq (by simp [s₄, harr₃ 13 (by decide)]))
        (by simp [s₄, State.setReg, hreg₃ 14 (by decide) (by decide) (by decide) (by decide), hrn])
        (by simp [s₄])
        hr21₄
        (by simp [s₄, hK_len₃])
        (fun i hi => hK_get₃ i hi) with
      ⟨s₅, t₅, hex₅, ht₅, hr21₅, hK_len₅, hK_get₅, harr₅, hreg₅⟩
    refine ⟨s₅, 3 + ((3 + (3 + t_b)) + 4) + t₅,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ hex_b)) hex_inc) hex₅,
      by omega, hr21₅, hK_len₅, hK_get₅,
      fun a ha => by rw [harr₅ a ha]; exact harr₃ a ha,
      fun r h2 h3 h4 h21 => by
        rw [hreg₅ r h2 h3 h4 h21]
        simp [s₄, State.setReg, h2, hreg₃ r h2 h3 h4 h21]⟩

theorem collectKProg_exec {w n : ℕ} (A B VB : Finset (Fin n))
    (hAB_iff : ∀ u : Fin n, u ∈ A ∩ B ↔ u ∈ B ∧ u ∈ VB)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hB : IsBitSet B 14 s) (hVB : IsBitSet VB 13 s)
    (hrn : s.regs 14 = n) :
    ∃ s' t,
      Exec w collectKProg s s' t ∧
      t ≤ 24 * n + 8 ∧
      s'.regs 21 = ((List.finRange n).filter (· ∈ A ∩ B)).length ∧
      (s'.arrs 16).length = n ∧
      (∀ i (hi : i < ((List.finRange n).filter (· ∈ A ∩ B)).length),
        (s'.arrs 16).getD i 0 = (((List.finRange n).filter (· ∈ A ∩ B))[i]'hi).1) ∧
      (∀ a : Arr, a ≠ 16 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 21 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 16 (List.replicate n 0)
  have hex₁ : Exec w (.alloc 16 (.reg 14)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg 21 0
  have hex₂ : Exec w (.assign 21 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg 2 0
  have hex₃ : Exec w (.assign 2 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hB₃ : IsBitSet B 14 s₃ := hB.of_arr_eq rfl
  have hVB₃ : IsBitSet VB 13 s₃ := hVB.of_arr_eq rfl
  have hrn₃ : s₃.regs 14 = n := hrn
  have hru₃ : s₃.regs 2 = 0 := rfl
  have hr21₃ : s₃.regs 21 = (((List.finRange n).take 0).filter (· ∈ A ∩ B)).length := rfl
  have hK_len₃ : (s₃.arrs 16).length = n := by simp [s₃, s₂, s₁]
  rcases collectKLoop_exec A B VB hAB_iff hw hn_w n 0 (by omega)
      hB₃ hVB₃ hrn₃ hru₃ hr21₃ hK_len₃ (fun i hi => by simp at hi) with
    ⟨s₄, t₄, hex₄, ht₄, hr21₄, hK_len₄, hK_get₄, harr₄, hreg₄⟩
  refine ⟨s₄, (1 + n) + (2 + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hr21₄, hK_len₄, hK_get₄,
    fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, ha],
    fun r h2 h3 h4 h21 => by
      rw [hreg₄ r h2 h3 h4 h21]
      simp [s₃, s₂, s₁, State.setReg, h2, h21]⟩

/-- Helper lemma for writing two consecutive words `[a, b]` immediately after `pref` inside
`pref ++ List.replicate (2 + m) 0`. -/
lemma set_two_append_replicate (pref : List ℕ) (a b m : ℕ) :
    ((pref ++ List.replicate (2 + m) 0).set pref.length a).set (pref.length + 1) b =
      (pref ++ [a, b]) ++ List.replicate m 0 := by
  have hrep : List.replicate (2 + m) 0 = 0 :: 0 :: List.replicate m 0 := by
    rw [Nat.add_comm 2 m, List.replicate_succ, List.replicate_succ]
  rw [hrep]
  rw [List.set_append_right _ _ (by omega)]
  have h0 : pref.length - pref.length = 0 := by omega
  rw [h0, List.set_cons_zero]
  rw [List.set_append_right _ _ (by omega)]
  have h1 : pref.length + 1 - pref.length = 1 := by omega
  rw [h1, List.set_cons_succ, List.set_cons_zero]
  simp [List.append_assoc]

lemma mem_flatEdges_lt {n : ℕ} (edges : List (Fin n × Fin n)) (v : ℕ)
    (hv : v ∈ flatEdges edges) : v < n := by
  rw [flatEdges, List.mem_flatMap] at hv
  rcases hv with ⟨e, _, hve⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hve
  rcases hve with rfl | rfl
  · exact e.1.2
  · exact e.2.2

/-- Loop body of `filterEdgesProg`: for edge `k = r_2 < r_1 = edges.length`, reads endpoints
`u := inArr[2 + 2 * k]` (`r_3`) and `w := inArr[3 + 2 * k]` (`r_4`), checks
`keepCoreEdge A B (u, w)` via `r_9 := (a_Z[u] * a_Z[w]) * (1 - a_VB[u] * a_VB[w])`,
and if non-zero appends `[u, w]` to `a_new = 17` at offset `2 + 2 * r_22` and increments `r_22`. -/
def filterEdgesBody : Cmd :=
  .seq (.assign 3 (.read 0 (.op .add (.const 2) (.op .mul (.const 2) (.reg 2)))))
    (.seq (.assign 4 (.read 0 (.op .add (.const 3) (.op .mul (.const 2) (.reg 2)))))
      (.seq (.assign 5 (.read 14 (.reg 3)))
        (.seq (.assign 6 (.read 14 (.reg 4)))
          (.seq (.assign 7 (.read 13 (.reg 3)))
            (.seq (.assign 8 (.read 13 (.reg 4)))
              (.seq (.assign 9 (.op .mul (.op .mul (.reg 5) (.reg 6))
                  (.op .sub (.const 1) (.op .mul (.reg 7) (.reg 8)))))
                (.ite (.reg 9)
                  (.seq (.write 17 (.op .add (.const 2) (.op .mul (.const 2) (.reg 22))) (.reg 3))
                    (.seq (.write 17 (.op .add (.const 3) (.op .mul (.const 2) (.reg 22))) (.reg 4))
                      (.assign 22 (.op .add (.reg 22) (.const 1)))))
                  .skip)))))))

def filterEdgesProg : Cmd :=
  .seq (.alloc 17 (.op .add (.const 8) (.op .mul (.const 2) (.reg 1))))
    (.seq (.assign 22 (.const 0))
      (.seq (.assign 2 (.const 0))
        (forUp 2 (.reg 1) filterEdgesBody)))

theorem filterEdgesLoop_exec {w n : ℕ} (A B VB : Finset (Fin n))
    (hAB_iff : ∀ u : Fin n, u ∈ A ∩ B ↔ u ∈ B ∧ u ∈ VB)
    (edges : List (Fin n × Fin n))
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm8_w : 8 + 2 * edges.length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = edges.length) {s : State}
    (hin : s.arrs 0 = [n, edges.length] ++ flatEdges edges)
    (hB : IsBitSet B 14 s) (hVB : IsBitSet VB 13 s)
    (hrm : s.regs 1 = edges.length) (hrk : s.regs 2 = k)
    (hr22 : s.regs 22 = ((edges.take k).filter (keepCoreEdge A B)).length)
    (hnew : s.arrs 17 =
      ([0, 0] ++ flatEdges ((edges.take k).filter (keepCoreEdge A B))) ++
        List.replicate (6 + 2 * (edges.length - ((edges.take k).filter (keepCoreEdge A B)).length)) 0) :
    let L₁ := edges.filter (keepCoreEdge A B)
    ∃ s' t,
      Exec w (forUp 2 (.reg 1) filterEdgesBody) s s' t ∧
      t ≤ 3 + 62 * rem ∧
      s'.regs 22 = L₁.length ∧
      s'.arrs 17 = ([0, 0] ++ flatEdges L₁) ++
        List.replicate (6 + 2 * (edges.length - L₁.length)) 0 ∧
      (∀ a : Arr, a ≠ 17 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 22 →
        s'.regs r = s.regs r) := by
  intro L₁
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = edges.length := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 2) (.reg 1)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, hm_w]
    have htake : edges.take edges.length = edges := List.take_of_length_le (by simp)
    rw [htake] at hr22 hnew
    exact ⟨s, 3, .while_false hcond, by omega, hr22, hnew,
      fun _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < edges.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have h2k_w : 2 * k < 2 ^ w := by omega
    have h2k2_w : 2 + 2 * k < 2 ^ w := by omega
    have h2k3_w : 3 + 2 * k < 2 ^ w := by omega
    let e := edges[k]'hk_lt
    let u := e.1
    let v := e.2
    let L_k := (edges.take k).filter (keepCoreEdge A B)
    let L_next := (edges.take (k + 1)).filter (keepCoreEdge A B)
    have hL_k_le : L_k.length ≤ k := by
      calc
        L_k.length ≤ (edges.take k).length := List.length_filter_le _ _
        _ = k := by rw [List.length_take]; omega
    have htake_succ : edges.take (k + 1) = edges.take k ++ [e] :=
      take_add_one_eq_append_getElem edges k hk_lt
    have hcond : (Expr.op .lt (.reg 2) (.reg 1)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, hk_w, hm_w, hk_lt, hw]
    have hin_u_lt : 2 + 2 * k < (s.arrs 0).length := by
      rw [hin]; simp [length_flatEdges]; omega
    have hin_u_get : (s.arrs 0)[2 + 2 * k]'hin_u_lt = u.1 := by
      have hidx : 2 + 2 * k = (2 * k) + 1 + 1 := by omega
      simp only [hin, hidx, List.cons_append, List.nil_append, List.getElem_cons_succ]
      exact getElem_flatEdges_even edges hk_lt
    have hin_v_lt : 3 + 2 * k < (s.arrs 0).length := by
      rw [hin]; simp [length_flatEdges]; omega
    have hin_v_get : (s.arrs 0)[3 + 2 * k]'hin_v_lt = v.1 := by
      have hidx : 3 + 2 * k = (2 * k + 1) + 1 + 1 := by omega
      simp only [hin, hidx, List.cons_append, List.nil_append, List.getElem_cons_succ]
      exact getElem_flatEdges_odd edges hk_lt
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    let s₁ := s.setReg 3 u.1
    have hex₁ : Exec w (.assign 3 (.read 0 (.op .add (.const 2) (.op .mul (.const 2) (.reg 2))))) s s₁ 7 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hw2, hk_w, h2k_w, h2k2_w,
          hin_u_lt, hin_u_get, hu_w])
    let s₂ := s₁.setReg 4 v.1
    have hex₂ : Exec w (.assign 4 (.read 0 (.op .add (.const 3) (.op .mul (.const 2) (.reg 2))))) s₁ s₂ 7 :=
      .assign (by
        simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hw2, hw3,
          hk_w, h2k_w, h2k3_w, hin_v_lt, hin_v_get, hv_w])
    have hu_B_lt : u.1 < (s.arrs 14).length := by rw [hB.1]; exact u.2
    let b_u := (s.arrs 14)[u.1]'hu_B_lt
    have hbu_eq : b_u = if u ∈ B then 1 else 0 := hB.getElem_eq_ite u
    have hbu_w : b_u < 2 ^ w := by rw [hbu_eq]; split_ifs <;> omega
    let s₃ := s₂.setReg 5 b_u
    have hex₃ : Exec w (.assign 5 (.read 14 (.reg 3))) s₂ s₃ 3 :=
      .assign (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hu_w, hu_B_lt, b_u, hbu_w])
    have hv_B_lt : v.1 < (s.arrs 14).length := by rw [hB.1]; exact v.2
    let b_v := (s.arrs 14)[v.1]'hv_B_lt
    have hbv_eq : b_v = if v ∈ B then 1 else 0 := hB.getElem_eq_ite v
    have hbv_w : b_v < 2 ^ w := by rw [hbv_eq]; split_ifs <;> omega
    let s₄ := s₃.setReg 6 b_v
    have hex₄ : Exec w (.assign 6 (.read 14 (.reg 4))) s₃ s₄ 3 :=
      .assign (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hv_w, hv_B_lt, b_v, hbv_w])
    have hu_VB_lt : u.1 < (s.arrs 13).length := by rw [hVB.1]; exact u.2
    let vb_u := (s.arrs 13)[u.1]'hu_VB_lt
    have hvbu_eq : vb_u = if u ∈ VB then 1 else 0 := hVB.getElem_eq_ite u
    have hvbu_w : vb_u < 2 ^ w := by rw [hvbu_eq]; split_ifs <;> omega
    let s₅ := s₄.setReg 7 vb_u
    have hex₅ : Exec w (.assign 7 (.read 13 (.reg 3))) s₄ s₅ 3 :=
      .assign (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hu_w, hu_VB_lt, vb_u, hvbu_w])
    have hv_VB_lt : v.1 < (s.arrs 13).length := by rw [hVB.1]; exact v.2
    let vb_v := (s.arrs 13)[v.1]'hv_VB_lt
    have hvbv_eq : vb_v = if v ∈ VB then 1 else 0 := hVB.getElem_eq_ite v
    have hvbv_w : vb_v < 2 ^ w := by rw [hvbv_eq]; split_ifs <;> omega
    let s₆ := s₅.setReg 8 vb_v
    have hex₆ : Exec w (.assign 8 (.read 13 (.reg 4))) s₅ s₆ 3 :=
      .assign (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hv_w, hv_VB_lt, vb_v, hvbv_w])
    let flag := (b_u * b_v) * (1 - vb_u * vb_v)
    have hflag_eq : flag = if keepCoreEdge A B e then 1 else 0 := by
      dsimp [flag, keepCoreEdge]
      rw [hbu_eq, hbv_eq, hvbu_eq, hvbv_eq]
      have huAB : u ∈ A ∩ B ↔ u ∈ B ∧ u ∈ VB := hAB_iff u
      have hvAB : v ∈ A ∩ B ↔ v ∈ B ∧ v ∈ VB := hAB_iff v
      by_cases h1 : u ∈ B <;> by_cases h2 : v ∈ B <;>
        by_cases h3 : u ∈ VB <;> by_cases h4 : v ∈ VB <;>
        simp [e, u, v, huAB, hvAB, h1, h2, h3, h4]
    have hbu_bv_w : b_u * b_v < 2 ^ w := by rw [hbu_eq, hbv_eq]; split_ifs <;> omega
    have hvbu_vbv_w : vb_u * vb_v < 2 ^ w := by rw [hvbu_eq, hvbv_eq]; split_ifs <;> omega
    have hsub_w : 1 - vb_u * vb_v < 2 ^ w := by rw [hvbu_eq, hvbv_eq]; split_ifs <;> omega
    have hflag_w : flag < 2 ^ w := by rw [hflag_eq]; split_ifs <;> omega
    let s₇ := s₆.setReg 9 flag
    have hex₇ : Exec w (.assign 9 (.op .mul (.op .mul (.reg 5) (.reg 6))
        (.op .sub (.const 1) (.op .mul (.reg 7) (.reg 8))))) s₆ s₇ 10 :=
      .assign (by
        simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hbu_w, hbv_w, hvbu_w, hvbv_w, hw, hbu_bv_w, hvbu_vbv_w, hsub_w, flag, hflag_w])
    have hstep : ∃ s₈ t_b,
        Exec w (.ite (.reg 9)
          (.seq (.write 17 (.op .add (.const 2) (.op .mul (.const 2) (.reg 22))) (.reg 3))
            (.seq (.write 17 (.op .add (.const 3) (.op .mul (.const 2) (.reg 22))) (.reg 4))
              (.assign 22 (.op .add (.reg 22) (.const 1)))))
          .skip) s₇ s₈ t_b ∧
        t_b ≤ 19 ∧
        s₈.regs 2 = k ∧
        s₈.regs 22 = L_next.length ∧
        s₈.arrs 17 = ([0, 0] ++ flatEdges L_next) ++
          List.replicate (6 + 2 * (edges.length - L_next.length)) 0 ∧
        (∀ a : Arr, a ≠ 17 → s₈.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 22 →
          s₈.regs r = s.regs r) := by
      by_cases hkeep : keepCoreEdge A B e = true
      · have hflag1 : flag = 1 := by simp [hflag_eq, hkeep]
        have hcond9 : (Expr.reg 9).eval w s₇ = some 1 := by
          simp [s₇, State.setReg, Expr.eval, checkWord, hflag1, hw]
        have hL_next_eq : L_next = L_k ++ [e] := by
          dsimp [L_next, L_k]
          rw [htake_succ, List.filter_append, List.filter_cons_of_pos hkeep, List.filter_nil]
        have hr22_s₇ : s₇.regs 22 = L_k.length := hr22
        have hL_w : L_k.length < 2 ^ w := by omega
        have h2L_w : 2 * L_k.length < 2 ^ w := by omega
        have h2L2_w : 2 + 2 * L_k.length < 2 ^ w := by omega
        have h2L3_w : 3 + 2 * L_k.length < 2 ^ w := by omega
        have hnew_len : (s.arrs 17).length = 8 + 2 * edges.length := by
          rw [hnew, List.length_append, List.length_append, length_flatEdges, List.length_replicate]
          simp only [List.length_cons, List.length_nil]
          change 2 + 2 * L_k.length + (6 + 2 * (edges.length - L_k.length)) = 8 + 2 * edges.length
          omega
        let s₇a := s₇.writeArr 17 (2 + 2 * L_k.length) u.1
        have hex_w1 : Exec w (.write 17 (.op .add (.const 2) (.op .mul (.const 2) (.reg 22))) (.reg 3)) s₇ s₇a 7 :=
          .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22_s₇, hw2, hL_w, h2L_w, h2L2_w])
            (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hu_w])
            (by change 2 + 2 * L_k.length < (s.arrs 17).length; omega)
        let s₇b := s₇a.writeArr 17 (3 + 2 * L_k.length) v.1
        have hr22_s₇a : s₇a.regs 22 = L_k.length := hr22
        have hex_w2 : Exec w (.write 17 (.op .add (.const 3) (.op .mul (.const 2) (.reg 22))) (.reg 4)) s₇a s₇b 7 :=
          .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22_s₇a, hw2, hw3, hL_w, h2L_w, h2L3_w])
            (by simp [s₇a, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hv_w])
            (by simp only [s₇a, State.writeArr_arrs_self, List.length_set]; change 3 + 2 * L_k.length < (s.arrs 17).length; omega)
        let s₈ := s₇b.setReg 22 (L_k.length + 1)
        have hr22_s₇b : s₇b.regs 22 = L_k.length := hr22
        have hex_inc22 : Exec w (.assign 22 (.op .add (.reg 22) (.const 1))) s₇b s₈ 4 :=
          .assign (by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22_s₇b, hL_w, hw,
              show L_k.length + 1 < 2 ^ w by omega])
        have hnew_s₈ : s₈.arrs 17 = ([0, 0] ++ flatEdges L_next) ++
            List.replicate (6 + 2 * (edges.length - L_next.length)) 0 := by
          change ((s.arrs 17).set (2 + 2 * L_k.length) u.1).set (3 + 2 * L_k.length) v.1 = _
          rw [hnew]
          change ((([0, 0] ++ flatEdges L_k) ++
            List.replicate (6 + 2 * (edges.length - L_k.length)) 0).set (2 + 2 * L_k.length) u.1).set
              (3 + 2 * L_k.length) v.1 = _
          have hplen : ([0, 0] ++ flatEdges L_k).length = 2 + 2 * L_k.length := by
            simp [length_flatEdges]; omega
          have hplen1 : ([0, 0] ++ flatEdges L_k).length + 1 = 3 + 2 * L_k.length := by omega
          have hrem_rep : 6 + 2 * (edges.length - L_k.length) =
              2 + (6 + 2 * (edges.length - (L_k.length + 1))) := by omega
          rw [← hplen1, ← hplen, hrem_rep, set_two_append_replicate]
          simp [hL_next_eq, flatEdges, e, u, v, List.append_assoc]
        refine ⟨s₈, 1 + (7 + (7 + 4)),
          .ite_true hcond9 (by decide) (.seq hex_w1 (.seq hex_w2 hex_inc22)),
          by omega, hrk, by simp [s₈, hL_next_eq], hnew_s₈,
          fun a ha => by simp [s₈, s₇b, s₇a, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha],
          fun r _ h3 h4 h5 h6 h7 h8 h9 h22 => by
            simp [s₈, s₇b, s₇a, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
              h3, h4, h5, h6, h7, h8, h9, h22]⟩
      · have hkeep_f : keepCoreEdge A B e = false := Bool.eq_false_iff.mpr hkeep
        have hflag0 : flag = 0 := by rw [hflag_eq, hkeep_f]; rfl
        have hcond9 : (Expr.reg 9).eval w s₇ = some 0 := by
          simp [s₇, State.setReg, Expr.eval, checkWord, hflag0, h0_w]
        have hL_next_eq : L_next = L_k := by
          dsimp [L_next, L_k]
          rw [htake_succ, List.filter_append, List.filter_cons_of_neg hkeep,
            List.filter_nil, List.append_nil]
        refine ⟨s₇, 1 + 1, .ite_false hcond9 (.skip s₇), by omega, hrk,
          by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hL_next_eq, hr22, L_k],
          by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL_next_eq, hnew, L_k],
          fun _ _ => rfl,
          fun r _ h3 h4 h5 h6 h7 h8 h9 _ => by
            simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, h3, h4, h5, h6, h7, h8, h9]⟩
    rcases hstep with ⟨s₈, t_b, hex_b, ht_b, hr2_s₈, hr22₈, hnew₈, harr₈, hreg₈⟩
    let s₉ := s₈.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₈ s₉ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_s₈, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have hin₉ : s₉.arrs 0 = [n, edges.length] ++ flatEdges edges := by
      change s₈.arrs 0 = _
      rw [harr₈ 0 (by decide), hin]
    have hB₉ : IsBitSet B 14 s₉ := hB.of_arr_eq (harr₈ 14 (by decide))
    have hVB₉ : IsBitSet VB 13 s₉ := hVB.of_arr_eq (harr₈ 13 (by decide))
    have hrm₉ : s₉.regs 1 = edges.length := by
      change s₈.regs 1 = _
      rw [hreg₈ 1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), hrm]
    have hrk₉ : s₉.regs 2 = k + 1 := by simp [s₉]
    have hr22₉ : s₉.regs 22 = L_next.length := hr22₈
    have hnew₉ : s₉.arrs 17 = ([0, 0] ++ flatEdges L_next) ++
        List.replicate (6 + 2 * (edges.length - L_next.length)) 0 := hnew₈
    rcases ih (k + 1) (by omega) hin₉ hB₉ hVB₉ hrm₉ hrk₉ hr22₉ hnew₉ with
      ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hr22₁₀, hnew₁₀, harr₁₀, hreg₁₀⟩
    refine ⟨s₁₀, 3 + ((7 + (7 + (3 + (3 + (3 + (3 + (10 + t_b))))))) + 4) + t₁₀,
      .while_true hcond (by omega)
        (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex_b))))))) hex_inc)
        hex₁₀,
      by omega, hr22₁₀, hnew₁₀,
      fun a ha => by rw [harr₁₀ a ha]; exact harr₈ a ha,
      fun r h2 h3 h4 h5 h6 h7 h8 h9 h22 => by
        rw [hreg₁₀ r h2 h3 h4 h5 h6 h7 h8 h9 h22]
        simp [s₉, State.setReg, h2, hreg₈ r h2 h3 h4 h5 h6 h7 h8 h9 h22]⟩

theorem filterEdgesProg_exec {w n : ℕ} (A B VB : Finset (Fin n))
    (hAB_iff : ∀ u : Fin n, u ∈ A ∩ B ↔ u ∈ B ∧ u ∈ VB)
    (edges : List (Fin n × Fin n))
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm8_w : 8 + 2 * edges.length < 2 ^ w) {s : State}
    (hin : s.arrs 0 = [n, edges.length] ++ flatEdges edges)
    (hB : IsBitSet B 14 s) (hVB : IsBitSet VB 13 s)
    (hrm : s.regs 1 = edges.length) :
    let L₁ := edges.filter (keepCoreEdge A B)
    ∃ s' t,
      Exec w filterEdgesProg s s' t ∧
      t ≤ 64 * edges.length + 22 ∧
      s'.regs 22 = L₁.length ∧
      s'.arrs 17 = ([0, 0] ++ flatEdges L₁) ++
        List.replicate (6 + 2 * (edges.length - L₁.length)) 0 ∧
      (∀ a : Arr, a ≠ 17 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 22 →
        s'.regs r = s.regs r) := by
  intro L₁
  have h0_w : 0 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h8_w : 8 < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  have h2m_w : 2 * edges.length < 2 ^ w := by omega
  let s₁ := s.setArr 17 (List.replicate (8 + 2 * edges.length) 0)
  have hex₁ : Exec w (.alloc 17 (.op .add (.const 8) (.op .mul (.const 2) (.reg 1)))) s s₁
      (5 + (8 + 2 * edges.length)) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm, h8_w, hw2, hm_w, h2m_w, hm8_w])
  let s₂ := s₁.setReg 22 0
  have hex₂ : Exec w (.assign 22 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg 2 0
  have hex₃ : Exec w (.assign 2 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hin₃ : s₃.arrs 0 = [n, edges.length] ++ flatEdges edges := hin
  have hB₃ : IsBitSet B 14 s₃ := hB.of_arr_eq rfl
  have hVB₃ : IsBitSet VB 13 s₃ := hVB.of_arr_eq rfl
  have hrm₃ : s₃.regs 1 = edges.length := hrm
  have hrk₃ : s₃.regs 2 = 0 := rfl
  have hr22₃ : s₃.regs 22 = ((edges.take 0).filter (keepCoreEdge A B)).length := rfl
  have hnew₃ : s₃.arrs 17 =
      ([0, 0] ++ flatEdges ((edges.take 0).filter (keepCoreEdge A B))) ++
        List.replicate (6 + 2 * (edges.length - ((edges.take 0).filter (keepCoreEdge A B)).length)) 0 := by
    change List.replicate (8 + 2 * edges.length) 0 = _
    simp only [List.take_zero, List.filter_nil, flatEdges, List.length_nil, Nat.sub_zero]
    rw [show 8 + 2 * edges.length = (6 + 2 * edges.length) + 2 by omega,
      Nat.add_comm _ 2, List.replicate_add]
    rfl
  rcases filterEdgesLoop_exec A B VB hAB_iff edges hw3 hn_w hm8_w edges.length 0 (by omega)
      hin₃ hB₃ hVB₃ hrm₃ hrk₃ hr22₃ hnew₃ with
    ⟨s₄, t₄, hex₄, ht₄, hr22₄, hnew₄, harr₄, hreg₄⟩
  refine ⟨s₄, (5 + (8 + 2 * edges.length)) + (2 + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hr22₄, hnew₄,
    fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, ha],
    fun r h2 h3 h4 h5 h6 h7 h8 h9 h22 => by
      rw [hreg₄ r h2 h3 h4 h5 h6 h7 h8 h9 h22]
      simp [s₃, s₂, s₁, State.setReg, h2, h22]⟩

/-- Append one edge `(r_u, r_w)` to `a_new = 17` at offset `2 + 2 * r_22` and increment `r_22`. -/
def appendEdgeTo17Prog (r_u r_w : Reg) : Cmd :=
  .seq (.write 17 (.op .add (.const 2) (.op .mul (.const 2) (.reg 22))) (.reg r_u))
    (.seq (.write 17 (.op .add (.const 3) (.op .mul (.const 2) (.reg 22))) (.reg r_w))
      (.assign 22 (.op .add (.reg 22) (.const 1))))

theorem appendEdgeTo17Prog_exec {w n : ℕ} (L : List (Fin n × Fin n)) (u v : Fin n)
    (r_u r_w : Reg) (_hne_u22 : r_u ≠ 22) (_hne_w22 : r_w ≠ 22) (rem_zeros : ℕ)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hL_w : 3 + 2 * L.length < 2 ^ w) {s : State}
    (hru : s.regs r_u = u.1) (hrw : s.regs r_w = v.1)
    (hr22 : s.regs 22 = L.length)
    (hnew : s.arrs 17 = ([0, 0] ++ flatEdges L) ++ List.replicate (2 + rem_zeros) 0) :
    ∃ s' t,
      Exec w (appendEdgeTo17Prog r_u r_w) s s' t ∧
      t ≤ 18 ∧
      s'.regs 22 = (L ++ [(u, v)]).length ∧
      s'.arrs 17 = ([0, 0] ++ flatEdges (L ++ [(u, v)])) ++ List.replicate rem_zeros 0 ∧
      (∀ a : Arr, a ≠ 17 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 22 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hL1_w : L.length < 2 ^ w := by omega
  have h2L_w : 2 * L.length < 2 ^ w := by omega
  have h2L2_w : 2 + 2 * L.length < 2 ^ w := by omega
  have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
  have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
  have hnew_len : (s.arrs 17).length = 2 + 2 * L.length + (2 + rem_zeros) := by
    rw [hnew, List.length_append, List.length_append, length_flatEdges, List.length_replicate]
    simp only [List.length_cons, List.length_nil]
  let s₁ := s.writeArr 17 (2 + 2 * L.length) u.1
  have hex₁ : Exec w (.write 17 (.op .add (.const 2) (.op .mul (.const 2) (.reg 22))) (.reg r_u)) s s₁ 7 :=
    .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22, hw2, hL1_w, h2L_w, h2L2_w])
      (by simp [Expr.eval, checkWord, hru, hu_w])
      (by rw [hnew_len]; omega)
  let s₂ := s₁.writeArr 17 (3 + 2 * L.length) v.1
  have hr22_1 : s₁.regs 22 = L.length := hr22
  have hrw_1 : s₁.regs r_w = v.1 := hrw
  have hex₂ : Exec w (.write 17 (.op .add (.const 3) (.op .mul (.const 2) (.reg 22))) (.reg r_w)) s₁ s₂ 7 :=
    .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22_1, hw2, hw3, hL1_w, h2L_w, hL_w])
      (by simp [Expr.eval, checkWord, hrw_1, hv_w])
      (by simp [s₁, hnew_len]; omega)
  let s₃ := s₂.setReg 22 (L.length + 1)
  have hr22_2 : s₂.regs 22 = L.length := hr22
  have hex₃ : Exec w (.assign 22 (.op .add (.reg 22) (.const 1))) s₂ s₃ 4 :=
    .assign (by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22_2, hL1_w, hw,
        show L.length + 1 < 2 ^ w by omega])
  have hnew₃ : s₃.arrs 17 = ([0, 0] ++ flatEdges (L ++ [(u, v)])) ++ List.replicate rem_zeros 0 := by
    change ((s.arrs 17).set (2 + 2 * L.length) u.1).set (3 + 2 * L.length) v.1 = _
    rw [hnew]
    have hplen : ([0, 0] ++ flatEdges L).length = 2 + 2 * L.length := by
      simp [length_flatEdges]; omega
    have hplen1 : ([0, 0] ++ flatEdges L).length + 1 = 3 + 2 * L.length := by omega
    rw [← hplen1, ← hplen, set_two_append_replicate]
    simp [flatEdges, List.append_assoc]
  refine ⟨s₃, 7 + (7 + 4), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by simp [s₃], hnew₃,
    fun a ha => by simp [s₃, s₂, s₁, ha],
    fun r hr => by simp [s₃, s₂, s₁, State.setReg, hr]⟩

/-- Append `(K[0], K[1])` to `a_new = 17` if `1 < r_21` (`1 < K.length`). -/
def appendClique1Prog : Cmd :=
  .ite (.op .lt (.const 1) (.reg 21))
    (.seq (.assign 3 (.read 16 (.const 0)))
      (.seq (.assign 4 (.read 16 (.const 1)))
        (appendEdgeTo17Prog 3 4)))
    .skip

/-- Append `(K[0], K[2])` and `(K[1], K[2])` to `a_new = 17` if `2 < r_21` (`2 < K.length`). -/
def appendClique2Prog : Cmd :=
  .ite (.op .lt (.const 2) (.reg 21))
    (.seq (.assign 3 (.read 16 (.const 0)))
      (.seq (.assign 4 (.read 16 (.const 1)))
        (.seq (.assign 5 (.read 16 (.const 2)))
          (.seq (appendEdgeTo17Prog 3 5)
            (appendEdgeTo17Prog 4 5)))))
    .skip

/-- Write header `[n, r_22]` to `a_new = 17`, update `r_1 := r_22`, set `r_21 := 2 + 2 * r_1`,
and copy `a_new[0 .. 2 + 2 * r_1)` into `inArr = 0` using `r_base = 22` (`21 < 22`). -/
def finalizeCoreEdgesProg : Cmd :=
  .seq (.write 17 (.const 0) (.reg 14))
    (.seq (.write 17 (.const 1) (.reg 22))
      (.seq (.assign 1 (.reg 22))
        (.seq (.assign 21 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))))
          (readSliceProg 17 (.const 0) 0 (.reg 21) 22))))

/-- Full core-step update of `(a_Z = 14, inArr = 0)` from `(Z, edges)` to
`(B, coreStepEdges A B edges)` where `A = Z ∩ VB`, `B = Z ∩ VA`, `a_VA = 12`, and `a_VB = 13`. -/
def updateCoreGraphProg : Cmd :=
  .seq (.assign 1 (.read 0 (.const 1)))
    (.seq updateZProg
      (.seq collectKProg
        (.seq filterEdgesProg
          (.seq appendClique1Prog
            (.seq appendClique2Prog
              finalizeCoreEdgesProg)))))

theorem appendClique1Prog_exec {w n : ℕ} (K : List (Fin n)) (L₁ : List (Fin n × Fin n))
    (rem_zeros : ℕ) (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hL_w : 3 + 2 * L₁.length < 2 ^ w)
    (hK_len_le : K.length ≤ n) {s : State}
    (hr21 : s.regs 21 = K.length)
    (hK_arr_len : (s.arrs 16).length = n)
    (hK_get : ∀ i (hi : i < K.length), (s.arrs 16).getD i 0 = (K[i]'hi).1)
    (hr22 : s.regs 22 = L₁.length)
    (hnew : s.arrs 17 = ([0, 0] ++ flatEdges L₁) ++ List.replicate (2 + rem_zeros) 0) :
    let P₁ := if h1 : 1 < K.length then [(K[0]'(by omega), K[1]'h1)] else []
    ∃ s' t,
      Exec w appendClique1Prog s s' t ∧
      t ≤ 29 ∧
      s'.regs 22 = (L₁ ++ P₁).length ∧
      s'.arrs 17 = ([0, 0] ++ flatEdges (L₁ ++ P₁)) ++
        List.replicate (if 1 < K.length then rem_zeros else 2 + rem_zeros) 0 ∧
      (∀ a : Arr, a ≠ 17 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 3 → r ≠ 4 → r ≠ 22 → s'.regs r = s.regs r) := by
  intro P₁
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hK_w : K.length < 2 ^ w := by omega
  by_cases h1 : 1 < K.length
  · have hcond : (Expr.op .lt (.const 1) (.reg 21)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr21, hw, hK_w, h1]
    have h0_arr : 0 < (s.arrs 16).length := by omega
    have h1_arr : 1 < (s.arrs 16).length := by omega
    have hget0 : (s.arrs 16)[0]'h0_arr = (K[0]'(by omega)).1 := by
      have h := hK_get 0 (by omega)
      change (s.arrs 16)[0]?.getD 0 = _ at h
      rwa [List.getElem?_eq_getElem h0_arr, Option.getD_some] at h
    have hget1 : (s.arrs 16)[1]'h1_arr = (K[1]'h1).1 := by
      have h := hK_get 1 h1
      change (s.arrs 16)[1]?.getD 0 = _ at h
      rwa [List.getElem?_eq_getElem h1_arr, Option.getD_some] at h
    have hk0_w : (K[0]'(by omega)).1 < 2 ^ w := Nat.lt_trans (K[0]'(by omega)).2 hn_w
    have hk1_w : (K[1]'h1).1 < 2 ^ w := Nat.lt_trans (K[1]'h1).2 hn_w
    let s₁ := s.setReg 3 (K[0]'(by omega)).1
    have hex₁ : Exec w (.assign 3 (.read 16 (.const 0))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, h0_w, h0_arr, hget0, hk0_w])
    let s₂ := s₁.setReg 4 (K[1]'h1).1
    have hex₂ : Exec w (.assign 4 (.read 16 (.const 1))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hw, h1_arr, hget1, hk1_w])
    rcases appendEdgeTo17Prog_exec L₁ (K[0]'(by omega)) (K[1]'h1) 3 4
        (by decide) (by decide) rem_zeros hw3 hn_w hL_w (s := s₂)
        (by simp [s₂, s₁, State.setReg]) (by simp [s₂])
        (by simp [s₂, s₁, State.setReg, hr22]) hnew with
      ⟨s₃, t₃, hex₃, ht₃, hr22₃, hnew₃, harr₃, hreg₃⟩
    have hP₁ : P₁ = [(K[0]'(by omega), K[1]'h1)] := by simp [P₁, h1]
    refine ⟨s₃, 3 + (3 + (3 + t₃)),
      .ite_true hcond (by decide) (.seq hex₁ (.seq hex₂ hex₃)),
      by omega, by rwa [hP₁], by simpa [hP₁, h1] using hnew₃,
      fun a ha => by rw [harr₃ a ha]; rfl,
      fun r h3 h4 h22 => by
        rw [hreg₃ r h22]
        simp [s₂, s₁, State.setReg, h3, h4]⟩
  · have hcond : (Expr.op .lt (.const 1) (.reg 21)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr21, hw, hK_w, h1, h0_w]
    have hP₁ : P₁ = [] := by simp [P₁, h1]
    refine ⟨s, 3 + 1, .ite_false hcond (.skip s), by omega,
      by simp [hP₁, hr22], by simpa [hP₁, h1] using hnew,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem appendClique2Prog_exec {w n : ℕ} (K : List (Fin n)) (L₁_P₁ : List (Fin n × Fin n))
    (rem_zeros : ℕ) (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hL_w : 5 + 2 * L₁_P₁.length < 2 ^ w)
    (hK_len_le : K.length ≤ n) {s : State}
    (hr21 : s.regs 21 = K.length)
    (hK_arr_len : (s.arrs 16).length = n)
    (hK_get : ∀ i (hi : i < K.length), (s.arrs 16).getD i 0 = (K[i]'hi).1)
    (hr22 : s.regs 22 = L₁_P₁.length)
    (hnew : s.arrs 17 = ([0, 0] ++ flatEdges L₁_P₁) ++ List.replicate (4 + rem_zeros) 0) :
    let P₂ := if h2 : 2 < K.length then [(K[0]'(by omega), K[2]'h2), (K[1]'(by omega), K[2]'h2)] else []
    ∃ s' t,
      Exec w appendClique2Prog s s' t ∧
      t ≤ 50 ∧
      s'.regs 22 = (L₁_P₁ ++ P₂).length ∧
      s'.arrs 17 = ([0, 0] ++ flatEdges (L₁_P₁ ++ P₂)) ++
        List.replicate (if 2 < K.length then rem_zeros else 4 + rem_zeros) 0 ∧
      (∀ a : Arr, a ≠ 17 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 22 → s'.regs r = s.regs r) := by
  intro P₂
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hK_w : K.length < 2 ^ w := by omega
  by_cases h2 : 2 < K.length
  · have h1 : 1 < K.length := by omega
    have hcond : (Expr.op .lt (.const 2) (.reg 21)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr21, hw, hw2, hK_w, h2]
    have h0_arr : 0 < (s.arrs 16).length := by omega
    have h1_arr : 1 < (s.arrs 16).length := by omega
    have h2_arr : 2 < (s.arrs 16).length := by omega
    have hget0 : (s.arrs 16)[0]'h0_arr = (K[0]'(by omega)).1 := by
      have h := hK_get 0 (by omega)
      change (s.arrs 16)[0]?.getD 0 = _ at h
      rwa [List.getElem?_eq_getElem h0_arr, Option.getD_some] at h
    have hget1 : (s.arrs 16)[1]'h1_arr = (K[1]'h1).1 := by
      have h := hK_get 1 h1
      change (s.arrs 16)[1]?.getD 0 = _ at h
      rwa [List.getElem?_eq_getElem h1_arr, Option.getD_some] at h
    have hget2 : (s.arrs 16)[2]'h2_arr = (K[2]'h2).1 := by
      have h := hK_get 2 h2
      change (s.arrs 16)[2]?.getD 0 = _ at h
      rwa [List.getElem?_eq_getElem h2_arr, Option.getD_some] at h
    have hk0_w : (K[0]'(by omega)).1 < 2 ^ w := Nat.lt_trans (K[0]'(by omega)).2 hn_w
    have hk1_w : (K[1]'h1).1 < 2 ^ w := Nat.lt_trans (K[1]'h1).2 hn_w
    have hk2_w : (K[2]'h2).1 < 2 ^ w := Nat.lt_trans (K[2]'h2).2 hn_w
    let s₁ := s.setReg 3 (K[0]'(by omega)).1
    have hex₁ : Exec w (.assign 3 (.read 16 (.const 0))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, h0_w, h0_arr, hget0, hk0_w])
    let s₂ := s₁.setReg 4 (K[1]'h1).1
    have hex₂ : Exec w (.assign 4 (.read 16 (.const 1))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hw, h1_arr, hget1, hk1_w])
    let s₃ := s₂.setReg 5 (K[2]'h2).1
    have hex₃ : Exec w (.assign 5 (.read 16 (.const 2))) s₂ s₃ 3 :=
      .assign (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hw2, h2_arr, hget2, hk2_w])
    have hnew₃ : s₃.arrs 17 = ([0, 0] ++ flatEdges L₁_P₁) ++ List.replicate (2 + (2 + rem_zeros)) 0 := by
      rw [show 4 + rem_zeros = 2 + (2 + rem_zeros) by omega] at hnew
      exact hnew
    rcases appendEdgeTo17Prog_exec L₁_P₁ (K[0]'(by omega)) (K[2]'h2) 3 5
        (by decide) (by decide) (2 + rem_zeros) hw3 hn_w (by omega)
        (by simp [s₃, s₂, s₁, State.setReg]) (by simp [s₃])
        (by simp [s₃, s₂, s₁, State.setReg, hr22]) hnew₃ with
      ⟨s₄, t₄, hex₄, ht₄, hr22₄, hnew₄, harr₄, hreg₄⟩
    have hr4_s₄ : s₄.regs 4 = (K[1]'h1).1 := by
      rw [hreg₄ 4 (by decide)]
      simp [s₃, s₂, State.setReg]
    have hr5_s₄ : s₄.regs 5 = (K[2]'h2).1 := by
      rw [hreg₄ 5 (by decide)]
      simp [s₃]
    rcases appendEdgeTo17Prog_exec (L₁_P₁ ++ [(K[0]'(by omega), K[2]'h2)]) (K[1]'h1) (K[2]'h2) 4 5
        (by decide) (by decide) rem_zeros hw3 hn_w (by simp; omega)
        hr4_s₄ hr5_s₄ hr22₄ hnew₄ with
      ⟨s₅, t₅, hex₅, ht₅, hr22₅, hnew₅, harr₅, hreg₅⟩
    have hP₂ : P₂ = [(K[0]'(by omega), K[2]'h2), (K[1]'h1, K[2]'h2)] := by simp [P₂, h2]
    have hlist_eq : (L₁_P₁ ++ [(K[0]'(by omega), K[2]'h2)]) ++ [(K[1]'h1, K[2]'h2)] =
        L₁_P₁ ++ P₂ := by simp [hP₂, List.append_assoc]
    refine ⟨s₅, 3 + (3 + (3 + (3 + (t₄ + t₅)))),
      .ite_true hcond (by decide) (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))),
      by omega, by rwa [← hlist_eq], by simpa [hlist_eq, h2] using hnew₅,
      fun a ha => by rw [harr₅ a ha, harr₄ a ha]; rfl,
      fun r h3 h4 h5 h22 => by
        rw [hreg₅ r h22, hreg₄ r h22]
        simp [s₃, s₂, s₁, State.setReg, h3, h4, h5]⟩
  · have hcond : (Expr.op .lt (.const 2) (.reg 21)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr21, hw2, hK_w, h2, h0_w]
    have hP₂ : P₂ = [] := by simp [P₂, h2]
    refine ⟨s, 3 + 1, .ite_false hcond (.skip s), by omega,
      by simp [hP₂, hr22], by simpa [hP₂, h2] using hnew,
      fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem finalizeCoreEdgesProg_exec {w n : ℕ} (edges' : List (Fin n × Fin n)) (rem_zeros : ℕ)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : 2 + 2 * edges'.length < 2 ^ w) {s : State}
    (hrn : s.regs 14 = n) (hr22 : s.regs 22 = edges'.length)
    (hnew : s.arrs 17 = ([0, 0] ++ flatEdges edges') ++ List.replicate rem_zeros 0) :
    ∃ s' t,
      Exec w finalizeCoreEdgesProg s s' t ∧
      t ≤ 32 * edges'.length + 55 ∧
      s'.arrs 0 = [n, edges'.length] ++ flatEdges edges' ∧
      s'.regs 1 = edges'.length ∧
      (∀ a : Arr, a ≠ 0 → a ≠ 17 → s'.arrs a = s.arrs a) ∧
      (∀ r < 21, r ≠ 1 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hm_w : edges'.length < 2 ^ w := by omega
  have h2m_w : 2 * edges'.length < 2 ^ w := by omega
  have hnew_len : 2 ≤ (s.arrs 17).length := by
    rw [hnew, List.length_append, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  let s₁ := s.writeArr 17 0 n
  have hex₁ : Exec w (.write 17 (.const 0) (.reg 14)) s s₁ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, hrn, hn_w])
      (by omega)
  let s₂ := s₁.writeArr 17 1 edges'.length
  have hr22_1 : s₁.regs 22 = edges'.length := hr22
  have hex₂ : Exec w (.write 17 (.const 1) (.reg 22)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [Expr.eval, checkWord, hr22_1, hm_w])
      (by simp [s₁]; omega)
  let s₃ := s₂.setReg 1 edges'.length
  have hr22_2 : s₂.regs 22 = edges'.length := hr22
  have hex₃ : Exec w (.assign 1 (.reg 22)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr22_2, hm_w])
  let s₄ := s₃.setReg 21 (2 + 2 * edges'.length)
  have hex₄ : Exec w (.assign 21 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))) s₃ s₄ 6 :=
    .assign (by simp [s₃, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hw2, hm_w, h2m_w, hm2_w])
  have hnew₄ : s₄.arrs 17 =
      [] ++ ([n, edges'.length] ++ flatEdges edges') ++ List.replicate rem_zeros 0 := by
    change ((s.arrs 17).set 0 n).set 1 edges'.length = _
    rw [hnew]
    simp
  have hslice_w : ∀ v ∈ [n, edges'.length] ++ flatEdges edges', v < 2 ^ w := by
    intro v hv
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl) | hv_flat
    · exact hn_w
    · exact hm_w
    · exact Nat.lt_trans (mem_flatEdges_lt edges' v hv_flat) hn_w
  rcases readSliceProg_exec (w := w) (n := 2 + 2 * edges'.length) (off := 0) 17 0 (.const 0) 21 22
      (by decide) (by decide)
      [] ([n, edges'.length] ++ flatEdges edges') (List.replicate rem_zeros 0)
      rfl (by simp [length_flatEdges]; omega) hslice_w hw (by omega)
      (by simp [Expr.eval, checkWord, h0_w])
      hnew₄ (by simp [s₄]) with
    ⟨s₅, t₅, hex₅, ht₅, harr0₅, harr_ne₅, hreg₅⟩
  dsimp [Expr.cost] at ht₅
  have ht₅_le : 3 + (3 + (2 + (6 + t₅))) ≤ 32 * edges'.length + 55 := by omega
  have hr1₅ : s₅.regs 1 = edges'.length := by
    rw [hreg₅ 1 (by decide)]
    simp [s₄, s₃]
  refine ⟨s₅, 3 + (3 + (2 + (6 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    ht₅_le, harr0₅, hr1₅,
    fun a ha0 ha17 => by
      rw [harr_ne₅ a ha0]
      simp [s₄, s₃, s₂, s₁, ha17],
    fun r hr h1 => by
      rw [hreg₅ r (Nat.lt_succ_of_lt hr)]
      have hne21 : (r : Reg) ≠ 21 := Nat.ne_of_lt hr
      simp [s₄, s₃, s₂, s₁, State.setReg, h1, hne21]⟩

theorem updateCoreGraphProg_exec {w n : ℕ} (Z VA VB : Finset (Fin n))
    (edges : List (Fin n × Fin n))
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm8_w : 8 + 2 * edges.length < 2 ^ w) {s : State}
    (hin : s.arrs 0 = [n, edges.length] ++ flatEdges edges)
    (hZ : IsBitSet Z 14 s) (hVA : IsBitSet VA 12 s) (hVB : IsBitSet VB 13 s)
    (hrn : s.regs 14 = n) :
    ∃ s' t,
      Exec w updateCoreGraphProg s s' t ∧
      t ≤ 39 * n + 96 * edges.length + 270 ∧
      IsBitSet (Z ∩ VA) 14 s' ∧
      s'.arrs 0 = [n, (coreStepEdges (Z ∩ VB) (Z ∩ VA) edges).length] ++
        flatEdges (coreStepEdges (Z ∩ VB) (Z ∩ VA) edges) ∧
      s'.regs 1 = (coreStepEdges (Z ∩ VB) (Z ∩ VA) edges).length ∧
      (∀ a : Arr, a ≠ 0 → a ≠ 14 → a ≠ 16 → a ≠ 17 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≥ 10 → r < 21 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  -- 0. r_1 := inArr[1]
  have h1_len : 1 < (s.arrs 0).length := by simp [hin, length_flatEdges]
  have h1_val : (s.arrs 0)[1]'h1_len = edges.length := by simp [hin]
  let s₀ := s.setReg 1 edges.length
  have hex₀ : Exec w (.assign 1 (.read 0 (.const 1))) s s₀ 3 :=
    .assign (by simp [Expr.eval, checkWord, hw, h1_len, h1_val, hm_w])
  have hAB_iff : ∀ u : Fin n, u ∈ (Z ∩ VB) ∩ (Z ∩ VA) ↔ u ∈ Z ∩ VA ∧ u ∈ VB := by
    intro u
    simp only [Finset.mem_inter]
    tauto
  -- 1. updateZProg
  rcases updateZProg_exec Z VA hw hn_w (s := s₀) (hZ.of_arr_eq rfl) (hVA.of_arr_eq rfl)
      (by simp [s₀, State.setReg, hrn]) with
    ⟨s₁, t₁, hex₁, ht₁, hB₁, harr₁, hreg₁⟩
  -- 2. collectKProg
  have hVB₁ : IsBitSet VB 13 s₁ := hVB.of_arr_eq (harr₁ 13 (by decide))
  have hrn₁ : s₁.regs 14 = n := by rw [hreg₁ 14 (by decide) (by decide)]; simp [s₀, hrn]
  rcases collectKProg_exec (Z ∩ VB) (Z ∩ VA) VB hAB_iff hw hn_w hB₁ hVB₁ hrn₁ with
    ⟨s₂, t₂, hex₂, ht₂, hr21₂, hK_len₂, hK_get₂, harr₂, hreg₂⟩
  -- 3. filterEdgesProg
  have hin₂ : s₂.arrs 0 = [n, edges.length] ++ flatEdges edges := by
    rw [harr₂ 0 (by decide), harr₁ 0 (by decide)]; exact hin
  have hB₂ : IsBitSet (Z ∩ VA) 14 s₂ := hB₁.of_arr_eq (harr₂ 14 (by decide))
  have hVB₂ : IsBitSet VB 13 s₂ := hVB₁.of_arr_eq (harr₂ 13 (by decide))
  have hrm₂ : s₂.regs 1 = edges.length := by
    rw [hreg₂ 1 (by decide) (by decide) (by decide) (by decide),
        hreg₁ 1 (by decide) (by decide)]
    simp [s₀]
  rcases filterEdgesProg_exec (Z ∩ VB) (Z ∩ VA) VB hAB_iff edges hw3 hn_w hm8_w
      hin₂ hB₂ hVB₂ hrm₂ with
    ⟨s₃, t₃, hex₃, ht₃, hr22₃, hnew₃, harr₃, hreg₃⟩
  -- 4. appendClique1Prog
  let K := (List.finRange n).filter (· ∈ (Z ∩ VB) ∩ (Z ∩ VA))
  let L₁ := edges.filter (keepCoreEdge (Z ∩ VB) (Z ∩ VA))
  have hL₁_le : L₁.length ≤ edges.length := List.length_filter_le _ _
  have hK_le : K.length ≤ n := by
    have := List.length_filter_le (· ∈ (Z ∩ VB) ∩ (Z ∩ VA)) (List.finRange n)
    rwa [List.length_finRange] at this
  have hr21₃ : s₃.regs 21 = K.length := by
    rw [hreg₃ 21 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hr21₂]
  have hK_len₃ : (s₃.arrs 16).length = n := by
    rw [harr₃ 16 (by decide), hK_len₂]
  have hK_get₃ : ∀ i (hi : i < K.length), (s₃.arrs 16).getD i 0 = (K[i]'hi).1 := by
    intro i hi
    rw [harr₃ 16 (by decide)]
    exact hK_get₂ i hi
  have hnew₃' : s₃.arrs 17 =
      ([0, 0] ++ flatEdges L₁) ++ List.replicate (2 + (4 + 2 * (edges.length - L₁.length))) 0 := by
    rw [show 2 + (4 + 2 * (edges.length - L₁.length)) = 6 + 2 * (edges.length - L₁.length) by omega]
    exact hnew₃
  rcases appendClique1Prog_exec K L₁ (4 + 2 * (edges.length - L₁.length))
      hw3 hn_w (by omega) hK_le hr21₃ hK_len₃ hK_get₃ hr22₃ hnew₃' with
    ⟨s₄, t₄, hex₄, ht₄, hr22₄, hnew₄, harr₄, hreg₄⟩
  -- 5. appendClique2Prog
  let P₁ := if h1 : 1 < K.length then [(K[0]'(by omega), K[1]'h1)] else []
  have hP₁_le : P₁.length ≤ 1 := by dsimp [P₁]; split_ifs <;> simp
  let rem₁ := if 1 < K.length then 2 * (edges.length - L₁.length) else 2 + 2 * (edges.length - L₁.length)
  have hrem₁_eq : (if 1 < K.length then 4 + 2 * (edges.length - L₁.length)
      else 2 + (4 + 2 * (edges.length - L₁.length))) = 4 + rem₁ := by
    dsimp [rem₁]; split_ifs <;> omega
  rw [hrem₁_eq] at hnew₄
  have hr21₄ : s₄.regs 21 = K.length := by
    rw [hreg₄ 21 (by decide) (by decide) (by decide), hr21₃]
  have hK_len₄ : (s₄.arrs 16).length = n := by
    rw [harr₄ 16 (by decide), hK_len₃]
  have hK_get₄ : ∀ i (hi : i < K.length), (s₄.arrs 16).getD i 0 = (K[i]'hi).1 := by
    intro i hi
    rw [harr₄ 16 (by decide)]
    exact hK_get₃ i hi
  have hLP₁_len : 5 + 2 * (L₁ ++ P₁).length < 2 ^ w := by
    rw [List.length_append]; omega
  rcases appendClique2Prog_exec K (L₁ ++ P₁) rem₁ hw3 hn_w hLP₁_len hK_le
      hr21₄ hK_len₄ hK_get₄ hr22₄ hnew₄ with
    ⟨s₅, t₅, hex₅, ht₅, hr22₅, hnew₅, harr₅, hreg₅⟩
  -- 6. finalizeCoreEdgesProg
  let P₂ := if h2 : 2 < K.length then [(K[0]'(by omega), K[2]'h2), (K[1]'(by omega), K[2]'h2)] else []
  have hedges'_eq : L₁ ++ P₁ ++ P₂ = coreStepEdges (Z ∩ VB) (Z ∩ VA) edges := by
    dsimp [coreStepEdges, cliquePairs, L₁, K, P₁, P₂]
    rw [List.append_assoc]
  rw [hedges'_eq] at hr22₅ hnew₅
  have hedges'_le : (coreStepEdges (Z ∩ VB) (Z ∩ VA) edges).length ≤ edges.length + 3 :=
    length_coreStepEdges_le (Z ∩ VB) (Z ∩ VA) edges
  have hrn₅ : s₅.regs 14 = n := by
    rw [hreg₅ 14 (by decide) (by decide) (by decide) (by decide),
        hreg₄ 14 (by decide) (by decide) (by decide),
        hreg₃ 14 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide),
        hreg₂ 14 (by decide) (by decide) (by decide) (by decide), hrn₁]
  rcases finalizeCoreEdgesProg_exec (coreStepEdges (Z ∩ VB) (Z ∩ VA) edges)
      (if 2 < K.length then rem₁ else 4 + rem₁)
      hw2 hn_w (by omega) hrn₅ hr22₅ hnew₅ with
    ⟨s₆, t₆, hex₆, ht₆, harr0₆, hr1₆, harr₆, hreg₆⟩
  have hB₆ : IsBitSet (Z ∩ VA) 14 s₆ := by
    refine hB₂.of_arr_eq ?_
    rw [harr₆ 14 (by decide) (by decide), harr₅ 14 (by decide),
        harr₄ 14 (by decide), harr₃ 14 (by decide)]
  have htime_upd : 3 + (t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆))))) ≤ 39 * n + 96 * edges.length + 270 := by
    linarith [ht₁, ht₂, ht₃, ht₄, ht₅, ht₆, hedges'_le]
  refine ⟨s₆, 3 + (t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆))))),
    .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆))))),
    htime_upd, hB₆, harr0₆, hr1₆,
    fun a ha0 ha14 ha16 ha17 => by
      rw [harr₆ a ha0 ha17, harr₅ a ha17, harr₄ a ha17, harr₃ a ha17,
        harr₂ a ha16, harr₁ a ha14]
      rfl,
    fun r hr10 hr21 => by
      have hne : ∀ k : Reg, ¬(k ≥ 10 ∧ k < 21) → r ≠ k :=
        fun k hk h => hk (h ▸ ⟨hr10, hr21⟩)
      rw [hreg₆ r hr21 (hne 1 (by decide)),
          hreg₅ r (hne 3 (by decide)) (hne 4 (by decide)) (hne 5 (by decide)) (hne 22 (by decide)),
          hreg₄ r (hne 3 (by decide)) (hne 4 (by decide)) (hne 22 (by decide)),
          hreg₃ r (hne 2 (by decide)) (hne 3 (by decide)) (hne 4 (by decide)) (hne 5 (by decide))
            (hne 6 (by decide)) (hne 7 (by decide)) (hne 8 (by decide)) (hne 9 (by decide)) (hne 22 (by decide)),
          hreg₂ r (hne 2 (by decide)) (hne 3 (by decide)) (hne 4 (by decide)) (hne 21 (by decide)),
          hreg₁ r (hne 2 (by decide)) (hne 3 (by decide))]
      simp [s₀, State.setReg, hne 1 (by decide)]⟩

/-! ### Syntactic Register and Array Preservation Helpers -/

/-- `c.preservesArr a` holds when command `c` contains no `.write a` or `.alloc a`. -/
def Cmd.preservesArr : Cmd → Arr → Bool
  | .skip, _ => true
  | .assign _ _, _ => true
  | .write a' _ _, a => a' != a
  | .alloc a' _, a => a' != a
  | .seq c₁ c₂, a => c₁.preservesArr a && c₂.preservesArr a
  | .ite _ c₁ c₂, a => c₁.preservesArr a && c₂.preservesArr a
  | .while _ body, a => body.preservesArr a

/-- `c.preservesReg r` holds when command `c` contains no `.assign r`. -/
def Cmd.preservesReg : Cmd → Reg → Bool
  | .skip, _ => true
  | .assign r' _, r => r' != r
  | .write _ _ _, _ => true
  | .alloc _ _, _ => true
  | .seq c₁ c₂, r => c₁.preservesReg r && c₂.preservesReg r
  | .ite _ c₁ c₂, r => c₁.preservesReg r && c₂.preservesReg r
  | .while _ body, r => body.preservesReg r

theorem Exec.arr_eq_of_preservesArr {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ}
    (hex : Exec w c s s' t) {a : Arr} (hp : c.preservesArr a = true) :
    s'.arrs a = s.arrs a := by
  induction hex with
  | skip => rfl
  | assign => rfl
  | write _ _ _ =>
    simp only [Cmd.preservesArr, bne_iff_ne, ne_eq] at hp
    exact State.writeArr_arrs_ne _ _ _ (Ne.symm hp)
  | alloc _ =>
    simp only [Cmd.preservesArr, bne_iff_ne, ne_eq] at hp
    exact State.setArr_arrs_ne _ _ (Ne.symm hp)
  | seq _ _ ih₁ ih₂ =>
    simp only [Cmd.preservesArr, Bool.and_eq_true] at hp
    rw [ih₂ hp.2, ih₁ hp.1]
  | ite_true _ _ _ ih =>
    simp only [Cmd.preservesArr, Bool.and_eq_true] at hp
    exact ih hp.1
  | ite_false _ _ ih =>
    simp only [Cmd.preservesArr, Bool.and_eq_true] at hp
    exact ih hp.2
  | while_false _ => rfl
  | while_true _ _ _ _ ih₁ ih₂ =>
    simp only [Cmd.preservesArr] at hp
    rw [ih₂ hp, ih₁ hp]

theorem Exec.reg_eq_of_preservesReg {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ}
    (hex : Exec w c s s' t) {r : Reg} (hp : c.preservesReg r = true) :
    s'.regs r = s.regs r := by
  induction hex with
  | skip => rfl
  | assign _ =>
    simp only [Cmd.preservesReg, bne_iff_ne, ne_eq] at hp
    exact State.setReg_regs_ne _ _ (Ne.symm hp)
  | write _ _ _ => rfl
  | alloc _ => rfl
  | seq _ _ ih₁ ih₂ =>
    simp only [Cmd.preservesReg, Bool.and_eq_true] at hp
    rw [ih₂ hp.2, ih₁ hp.1]
  | ite_true _ _ _ ih =>
    simp only [Cmd.preservesReg, Bool.and_eq_true] at hp
    exact ih hp.1
  | ite_false _ _ ih =>
    simp only [Cmd.preservesReg, Bool.and_eq_true] at hp
    exact ih hp.2
  | while_false _ => rfl
  | while_true _ _ _ _ ih₁ ih₂ =>
    simp only [Cmd.preservesReg] at hp
    rw [ih₂ hp, ih₁ hp]

/-! ## Section 3: Initialization and Main Vertex Loop of Algorithm (8.3) -/

/-- Loop body for building `IsBitSet x.omega.toFinset 9` from `inArr`:
reads `v := inArr[r_3 + r_2]` into `r_5` and sets `a_9[r_5] := 1`. -/
def buildOmegaBitSetBody : Cmd :=
  .seq (.assign 5 (.read 0 (.op .add (.reg 3) (.reg 2))))
    (.write 9 (.reg 5) (.const 1))

/-- Program that builds `IsBitSet x.omega.toFinset 9` from `inArr = encAlg81In x`
(assuming `r_1 = (edgeListOf x.G).length` and `r_14 = x.n`). -/
def buildOmegaBitSetProg : Cmd :=
  .seq (.alloc 9 (.reg 14))
    (.seq (.assign 3 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))))
      (.seq (.assign 4 (.read 0 (.reg 3)))
        (.seq (.assign 3 (.op .add (.reg 3) (.const 1)))
          (.seq (.assign 2 (.const 0))
            (forUp 2 (.reg 4) buildOmegaBitSetBody)))))

/-- Initialization program for Algorithm (8.3) from `inArr = encAlg81In x`:
1. Reads `r_0 = x.n`, `r_1 = m₀`, and sets `ConstRegs x.n 4 2` (`r_14 = x.n`, `r_15 = 2 * x.n`,
   `r_16 = 4`).
2. Builds `IsBitSet x.omega.toFinset 9` in array `9` (`buildOmegaBitSetProg`).
3. Truncates `inArr = 0` to `[x.n, m₀] ++ flatEdges (edgeListOf x.G)` using scratch array `17`.
4. Initializes `a_Z = 14` to `IsBitSet Finset.univ 14` (`initUnivBitSetProg 14`). -/
def initAlg83Prog : Cmd :=
  .seq (.assign 0 (.read 0 (.const 0)))
    (.seq (.assign 1 (.read 0 (.const 1)))
      (.seq (.assign 14 (.reg 0))
        (.seq (.assign 15 (.op .mul (.const 2) (.reg 14)))
          (.seq (.assign 16 (.const 4))
            (.seq buildOmegaBitSetProg
              (.seq (.assign 21 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))))
                (.seq (readSliceProg 0 (.const 0) 17 (.reg 21) 22)
                  (.seq (readSliceProg 17 (.const 0) 0 (.reg 21) 22)
                    (alg83InitUnivProg 14)))))))))

theorem buildOmegaBitSetLoop_exec {w : ℕ} (x : Alg81Input)
    (hw : 1 < 2 ^ w) (hn_w : x.n < 2 ^ w)
    (hin_w : 3 + 2 * (edgeListOf x.G).length + x.omega.length < 2 ^ w) :
    ∀ rem k (_hrem : k + rem = x.omega.length) {s : State}
      (_hin : s.arrs 0 = encAlg81In x)
      (_hr2 : s.regs 2 = k)
      (_hr3 : s.regs 3 = 3 + 2 * (edgeListOf x.G).length)
      (_hr4 : s.regs 4 = x.omega.length)
      (_hbit : IsBitSet (x.omega.take k).toFinset 9 s),
      ∃ s' t,
        Exec w (forUp 2 (.reg 4) buildOmegaBitSetBody) s s' t ∧
        t ≤ 15 * rem + 3 ∧
        IsBitSet x.omega.toFinset 9 s' ∧
        (∀ a : Arr, a ≠ 9 → s'.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ 2 → r ≠ 5 → s'.regs r = s.regs r)
  | 0, k, hrem, s, _, hr2, _, hr4, hbit => by
    have hk_eq : k = x.omega.length := by omega
    subst hk_eq
    have h0_w : 0 < 2 ^ w := by omega
    have hk_w : x.omega.length < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 2) (.reg 4)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr4, hk_w, h0_w]
    rw [List.take_length] at hbit
    exact ⟨s, 3, .while_false hcond, by omega, hbit, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | rem + 1, k, hrem, s, hin, hr2, hr3, hr4, hbit => by
    have hk_lt : k < x.omega.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hlen_w : x.omega.length < 2 ^ w := by omega
    have hr3_w : 3 + 2 * (edgeListOf x.G).length < 2 ^ w := by omega
    have hidx_w : (3 + 2 * (edgeListOf x.G).length) + k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 2) (.reg 4)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr4, hk_w, hlen_w, hk_lt, hw]
    obtain ⟨hlen_in, _, _, _, _, hget_om⟩ := inArr_getElem_alg81 x
    have hidx_in : 3 + 2 * (edgeListOf x.G).length + k < (s.arrs 0).length := by
      rw [hin, hlen_in]; omega
    have hval_in : (s.arrs 0)[3 + 2 * (edgeListOf x.G).length + k]'hidx_in = (x.omega[k]'hk_lt).1 := by
      simp only [hin]
      exact hget_om k hk_lt
    have hv_w : (x.omega[k]'hk_lt).1 < 2 ^ w := Nat.lt_trans (x.omega[k]'hk_lt).2 hn_w
    let s₁ := s.setReg 5 (x.omega[k]'hk_lt).1
    have hex₁ : Exec w (.assign 5 (.read 0 (.op .add (.reg 3) (.reg 2)))) s s₁ 5 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr2, hr3_w, hk_w,
        hidx_w, hidx_in, hval_in, hv_w])
    let s₂ := s₁.writeArr 9 (x.omega[k]'hk_lt).1 1
    have hex₂ : Exec w (.write 9 (.reg 5) (.const 1)) s₁ s₂ 3 :=
      .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hv_w])
        (by simp [Expr.eval, checkWord, hw])
        (by simp [s₁, hbit.1, (x.omega[k]'hk_lt).2])
    let s₃ := s₂.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr2, hk_w, hw, show k + 1 < 2 ^ w by omega])
    have hbit₃ : IsBitSet (x.omega.take (k + 1)).toFinset 9 s₃ := by
      have h1 : IsBitSet (insert (x.omega[k]'hk_lt) (x.omega.take k).toFinset) 9 s₂ :=
        (hbit.of_arr_eq rfl).write_one (x.omega[k]'hk_lt)
      have htake : (x.omega.take (k + 1)).toFinset =
          insert (x.omega[k]'hk_lt) (x.omega.take k).toFinset := by
        ext u
        simp only [Finset.mem_insert, List.mem_toFinset]
        rw [take_add_one_eq_append_getElem x.omega k hk_lt, List.mem_append, List.mem_singleton]
        tauto
      rw [← htake] at h1
      exact h1.of_arr_eq rfl
    rcases buildOmegaBitSetLoop_exec x hw hn_w hin_w rem (k + 1) (by omega)
        (by simp [s₃, s₂, s₁, hin])
        (by simp [s₃])
        (by simp [s₃, s₂, s₁, State.setReg, hr3])
        (by simp [s₃, s₂, s₁, State.setReg, hr4])
        hbit₃ with
      ⟨s₄, t₄, hex₄, ht₄, hbit₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((5 + 3) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex_inc) hex₄,
      by omega, hbit₄,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, ha],
      fun r h2 h5 => by
        rw [hreg₄ r h2 h5]
        simp [s₃, s₂, s₁, State.setReg, h2, h5]⟩

theorem buildOmegaBitSetProg_exec {w : ℕ} (x : Alg81Input)
    (hw2 : 2 < 2 ^ w) (hn_w : x.n < 2 ^ w)
    (hin_w : 3 + 2 * (edgeListOf x.G).length + x.omega.length < 2 ^ w) {s : State}
    (hin : s.arrs 0 = encAlg81In x)
    (hr1 : s.regs 1 = (edgeListOf x.G).length)
    (hr14 : s.regs 14 = x.n) :
    ∃ s' t,
      Exec w buildOmegaBitSetProg s s' t ∧
      t ≤ x.n + 15 * x.omega.length + 19 ∧
      IsBitSet x.omega.toFinset 9 s' ∧
      (∀ a : Arr, a ≠ 9 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hm_w : (edgeListOf x.G).length < 2 ^ w := by omega
  have h2m_w : 2 * (edgeListOf x.G).length < 2 ^ w := by omega
  have h22m_w : 2 + 2 * (edgeListOf x.G).length < 2 ^ w := by omega
  have h32m_w : 3 + 2 * (edgeListOf x.G).length < 2 ^ w := by omega
  have hk_w : x.omega.length < 2 ^ w := by omega
  obtain ⟨hlen_in, _, _, hget_k, _, _⟩ := inArr_getElem_alg81 x
  let s₁ := s.setArr 9 (List.replicate x.n 0)
  have hex₁ : Exec w (.alloc 9 (.reg 14)) s s₁ (1 + x.n) :=
    .alloc (by simp [Expr.eval, checkWord, hr14, hn_w])
  let s₂ := s₁.setReg 3 (2 + 2 * (edgeListOf x.G).length)
  have hex₂ : Exec w (.assign 3 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))) s₁ s₂ 6 :=
    .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1, hw2, hm_w, h2m_w, h22m_w])
  have hidx_k : 2 + 2 * (edgeListOf x.G).length < (s.arrs 0).length := by
    rw [hin, hlen_in]; omega
  have hval_k : (s.arrs 0)[2 + 2 * (edgeListOf x.G).length]'hidx_k = x.omega.length := by
    simp only [hin]
    exact hget_k
  let s₃ := s₂.setReg 4 x.omega.length
  have hex₃ : Exec w (.assign 4 (.read 0 (.reg 3))) s₂ s₃ 3 :=
    .assign (by simp [s₂, s₁, Expr.eval, checkWord, h22m_w, hidx_k, hval_k, hk_w])
  let s₄ := s₃.setReg 3 (3 + 2 * (edgeListOf x.G).length)
  have hex₄ : Exec w (.assign 3 (.op .add (.reg 3) (.const 1))) s₃ s₄ 4 :=
    .assign (by
      have hadd : (2 + 2 * (edgeListOf x.G).length) + 1 = 3 + 2 * (edgeListOf x.G).length := by omega
      simp [s₃, s₂, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        h22m_w, hw, hadd, h32m_w])
  let s₅ := s₄.setReg 2 0
  have hex₅ : Exec w (.assign 2 (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hbit₅ : IsBitSet (x.omega.take 0).toFinset 9 s₅ := by
    simp only [List.take_zero, List.toFinset_nil]
    exact IsBitSet.empty_of_replicate (by simp [s₅, s₄, s₃, s₂, s₁])
  rcases buildOmegaBitSetLoop_exec x hw hn_w hin_w x.omega.length 0 (by omega) (s := s₅)
      hin (by simp [s₅]) (by simp [s₅, s₄]) (by simp [s₅, s₄, s₃, State.setReg]) hbit₅ with
    ⟨s₆, t₆, hex₆, ht₆, hbit₆, harr₆, hreg₆⟩
  refine ⟨s₆, (1 + x.n) + (6 + (3 + (4 + (2 + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hbit₆,
    fun a ha => by rw [harr₆ a ha]; simp [s₅, s₄, s₃, s₂, s₁, ha],
    fun r h2 h3 h4 h5 => by
      rw [hreg₆ r h2 h5]
      simp [s₅, s₄, s₃, s₂, s₁, State.setReg, h2, h3, h4]⟩

theorem initAlg83Prog_exec {w : ℕ} (x : Alg81Input)
    (hw4 : 4 < 2 ^ w) (h2n_w : 2 * x.n < 2 ^ w)
    (hin_w : 3 + 2 * (edgeListOf x.G).length + x.omega.length < 2 ^ w) {s : State}
    (hin : s.arrs 0 = encAlg81In x) :
    let edges₀ := edgeListOf x.G
    ∃ s' t,
      Exec w initAlg83Prog s s' t ∧
      t ≤ 13 * x.n + 64 * edges₀.length + 15 * x.omega.length + 130 ∧
      s'.arrs 0 = [x.n, edges₀.length] ++ flatEdges edges₀ ∧
      IsBitSet x.omega.toFinset 9 s' ∧
      IsBitSet (Finset.univ : Finset (Fin x.n)) 14 s' ∧
      ConstRegs x.n 4 2 s' ∧
      s'.regs 0 = x.n ∧
      s'.regs 1 = edges₀.length := by
  intro edges₀
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hm_w : edges₀.length < 2 ^ w := by dsimp [edges₀]; omega
  have h2m_w : 2 * edges₀.length < 2 ^ w := by dsimp [edges₀]; omega
  have h22m_w : 2 + 2 * edges₀.length < 2 ^ w := by dsimp [edges₀]; omega
  obtain ⟨hlen_in, hget0, hget1, _, _, _⟩ := inArr_getElem_alg81 x
  -- 1. r_0 := inArr[0], r_1 := inArr[1], r_14 := r_0, r_15 := 2 * r_14, r_16 := 4
  have h0_idx : 0 < (s.arrs 0).length := by rw [hin, hlen_in]; omega
  have h0_val : (s.arrs 0)[0]'h0_idx = x.n := by simp only [hin]; exact hget0
  have h1_idx : 1 < (s.arrs 0).length := by rw [hin, hlen_in]; omega
  have h1_val : (s.arrs 0)[1]'h1_idx = edges₀.length := by simp only [hin, edges₀]; exact hget1
  let s₁ := s.setReg 0 x.n
  have hex₁ : Exec w (.assign 0 (.read 0 (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_idx, h0_val, hn_w])
  let s₂ := s₁.setReg 1 edges₀.length
  have hex₂ : Exec w (.assign 1 (.read 0 (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hw, h1_idx, h1_val, hm_w])
  let s₃ := s₂.setReg 14 x.n
  have hex₃ : Exec w (.assign 14 (.reg 0)) s₂ s₃ 2 :=
    .assign (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hn_w])
  let s₄ := s₃.setReg 15 (2 * x.n)
  have hex₄ : Exec w (.assign 15 (.op .mul (.const 2) (.reg 14))) s₃ s₄ 4 :=
    .assign (by simp [s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hn_w, h2n_w])
  let s₅ := s₄.setReg 16 4
  have hex₅ : Exec w (.assign 16 (.const 4)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw4])
  -- 2. buildOmegaBitSetProg
  rcases buildOmegaBitSetProg_exec x hw2 hn_w hin_w (s := s₅)
      hin
      (by simp [s₅, s₄, s₃, s₂, State.setReg, edges₀])
      (by simp [s₅, s₄, s₃, State.setReg]) with
    ⟨s₆, t₆, hex₆, ht₆, hom₆, harr₆, hreg₆⟩
  have hr1_₆ : s₆.regs 1 = edges₀.length := by
    rw [hreg₆ 1 (by decide) (by decide) (by decide) (by decide)]
    simp [s₅, s₄, s₃, s₂, State.setReg]
  -- 3. r_21 := 2 + 2 * r_1, readSliceProg 0 -> 17 -> 0
  let s₇ := s₆.setReg 21 (2 + 2 * edges₀.length)
  have hex₇ : Exec w (.assign 21 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))) s₆ s₇ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_₆, hw2, hm_w, h2m_w, h22m_w])
  have hin₇ : s₇.arrs 0 =
      [] ++ ([x.n, edges₀.length] ++ flatEdges edges₀) ++
        ([x.omega.length] ++ x.omega.map Fin.val) := by
    change s₆.arrs 0 = _
    rw [harr₆ 0 (by decide)]
    simpa [s₅, s₄, s₃, s₂, s₁, encAlg81In, encGraph, edges₀, List.append_assoc] using hin
  have hslice_w : ∀ v ∈ [x.n, edges₀.length] ++ flatEdges edges₀, v < 2 ^ w := by
    intro v hv
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl) | hv_flat
    · exact hn_w
    · exact hm_w
    · exact Nat.lt_trans (mem_flatEdges_lt edges₀ v hv_flat) hn_w
  rcases readSliceProg_exec (w := w) (n := 2 + 2 * edges₀.length) (off := 0) 0 17 (.const 0) 21 22
      (by decide) (by decide)
      [] ([x.n, edges₀.length] ++ flatEdges edges₀) ([x.omega.length] ++ x.omega.map Fin.val)
      rfl (by simp [length_flatEdges]; omega) hslice_w hw (by omega)
      (by simp [Expr.eval, checkWord, h0_w])
      hin₇ (by simp [s₇]) with
    ⟨s₈, t₈, hex₈, ht₈, harr17_₈, harr₈, hreg₈⟩
  dsimp [Expr.cost] at ht₈
  have harr17_₈' : s₈.arrs 17 = [] ++ ([x.n, edges₀.length] ++ flatEdges edges₀) ++ [] := by
    simpa using harr17_₈
  have hr21_₈ : s₈.regs 21 = 2 + 2 * edges₀.length := by
    rw [hreg₈ 21 (by decide)]
    simp [s₇]
  rcases readSliceProg_exec (w := w) (n := 2 + 2 * edges₀.length) (off := 0) 17 0 (.const 0) 21 22
      (by decide) (by decide)
      [] ([x.n, edges₀.length] ++ flatEdges edges₀) []
      rfl (by simp [length_flatEdges]; omega) hslice_w hw (by omega)
      (by simp [Expr.eval, checkWord, h0_w])
      harr17_₈' hr21_₈ with
    ⟨s₉, t₉, hex₉, ht₉, harr0_₉, harr₉, hreg₉⟩
  dsimp [Expr.cost] at ht₉
  -- 4. alg83InitUnivProg 14
  have hr14_₉ : s₉.regs 14 = x.n := by
    rw [hreg₉ 14 (by decide), hreg₈ 14 (by decide)]
    change s₆.regs 14 = x.n
    rw [hreg₆ 14 (by decide) (by decide) (by decide) (by decide)]
    simp [s₅, s₄, s₃, State.setReg]
  rcases alg83InitUnivProg_exec 14 hw hn_w hr14_₉ with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hZ₁₀, harr₁₀, hreg₁₀⟩
  have hkeep_reg : ∀ r : Reg, r < 21 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → s₁₀.regs r = s₅.regs r := by
    intro r hr21 h2 h3 h4 h5
    rw [hreg₁₀ r h2, hreg₉ r (Nat.lt_succ_of_lt hr21), hreg₈ r (Nat.lt_succ_of_lt hr21)]
    have hne21 : (r : Reg) ≠ 21 := Nat.ne_of_lt hr21
    have hs₇ : s₇.regs r = s₆.regs r := by
      simp [s₇, State.setReg, hne21]
    rw [hs₇]
    exact hreg₆ r h2 h3 h4 h5
  have htime_init : 3 + (3 + (2 + (4 + (2 + (t₆ + (6 + (t₈ + (t₉ + t₁₀)))))))) ≤
      13 * x.n + 64 * edges₀.length + 15 * x.omega.length + 130 := by
    linarith [ht₆, ht₈, ht₉, ht₁₀]
  refine ⟨s₁₀, 3 + (3 + (2 + (4 + (2 + (t₆ + (6 + (t₈ + (t₉ + t₁₀)))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
      (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))),
    htime_init,
    by rw [harr₁₀ 0 (by decide), harr0_₉],
    hom₆.of_arr_eq (by rw [harr₁₀ 9 (by decide), harr₉ 9 (by decide), harr₈ 9 (by decide)]; rfl),
    hZ₁₀,
    ⟨by rw [hkeep_reg 14 (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [s₅, s₄, s₃],
     by rw [hkeep_reg 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [s₅, s₄],
     by rw [hkeep_reg 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [s₅]⟩,
    by rw [hkeep_reg 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
       simp [s₅, s₄, s₃, s₂, s₁],
    by rw [hkeep_reg 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
       simp [s₅, s₄, s₃, s₂]⟩

/-- Program executed for vertex `v` (`r_20 = v.1`) when `v ∈ Z \ x.omega.toFinset`:
1. Parses the current core graph `C` from `inArr = 0` into CSR arrays `(3, 4, 5)` (`parseGraphProg 2 3 4 5 0`).
2. Builds `IsBitSet {v} 15` (`setSingletonBitSetProg 14 20 15`).
3. Builds `IsBitSet (Finset.univ \ {v}) 10` and `IsBitSet (extNeighborhood C {v}) 11`
   (`buildComplAndExtNhdProg 3 4 5 15 10 11`).
4. Sets `r_19 := 2 * r_1` and restricts `C` to `Finset.univ \ {v}` in CSR arrays `(6, 7, 8)`
   (`restrictGraphProg 3 4 5 10 6 7 8 14 19 2 3 4 5 6 7 8`).
5. Runs `initPathSystemRegProg 18 2` and `mengerLoopRegProg 6 7 8 11 9 18 2` with `k_goal = 4`
   (`r_16 = 4`).
6. If `r_18 = 0` (`< 4` paths found), builds `(VA, VB)` in arrays `(12, 13)`
   (`buildCandSepProg 15 21 12 13`) and updates `(Z, C)` to `(B, coreStepGraph C A B)`
   (`updateCoreGraphProg`). -/
def alg83ActiveVertexProg : Cmd :=
  .seq (parseGraphProg 2 3 4 5 0)
    (.seq (alg83SingletonProg 15 14 20)
      (.seq (buildComplAndExtNhdProg 3 4 5 15 10 11)
        (.seq (.assign 19 (.op .mul (.const 2) (.reg 1)))
          (.seq (restrictGraphProg 3 4 5 10 6 7 8 14 19 2 3 4 5 6 7 8)
            (.seq (.assign 17 (.const 0))
              (.seq (.assign 18 (.const 1))
                (.seq (initPathSystemRegProg 18 2)
                  (.seq (mengerLoopRegProg 6 7 8 11 9 18 2)
                    (.ite (.reg 18)
                      .skip
                      (.seq (buildCandSepProg 15 21 12 13)
                        updateCoreGraphProg))))))))))

/-- Single-vertex step of Algorithm (8.3) for vertex `v` (`r_20 = v.1`):
reads `a_Z[v]` and `a_omega[v]`; if `v ∈ Z \ x.omega.toFinset` (`a_Z[v] - a_omega[v] = 1`),
runs `alg83ActiveVertexProg`. -/
def alg83VertexStepProg : Cmd :=
  .seq (.assign 2 (.read 14 (.reg 20)))
    (.seq (.assign 3 (.read 9 (.reg 20)))
      (.seq (.assign 2 (.op .sub (.reg 2) (.reg 3)))
        (.ite (.reg 2) alg83ActiveVertexProg .skip)))

/-- Main vertex loop of Algorithm (8.3) over `v = 0 .. n - 1` (`r_20` from `0` to `r_14`). -/
def alg83LoopProg : Cmd :=
  .seq (.assign 20 (.const 0))
    (forUp 20 (.reg 14) alg83VertexStepProg)

/-- Every vertex `v ∈ Z` that is 4-linked in a core `(Z, C)` admits four `({v}, Ω)`-paths in `C`
that are pairwise vertex-disjoint except at `v` (`FourLinkedPaths omega Z C v`). -/
theorem fourLinkedPaths_of_isFourLinkedAt {n : ℕ} (omega : List (Fin n)) (Z : Finset (Fin n))
    (C : SimpleGraph (Fin n)) (v : Fin n)
    (hcore_om : omega.toFinset ⊆ Z)
    (hcore_adj : ∀ a b : Fin n, C.Adj a b → a ∈ Z ∧ b ∈ Z)
    (hvZ : v ∈ Z) (h4 : IsFourLinkedAt omega Z C v) :
    Nonempty (FourLinkedPaths omega Z C v) := by
  classical
  by_cases hv_om : v ∈ omega.toFinset
  · exact ⟨fourLinkedPaths_of_mem_omega (omega := omega) (Z := Z) (C := C) hvZ hv_om⟩
  · let G' := restrictGraph C (Finset.univ \ ({v} : Finset (Fin n)))
    let edges' := edgeListOf G'
    have hedges' : IsSimpleEdgeList G' edges' := isSimpleEdgeList_edgeListOf G'
    let w := wordSize 3 (n + edges'.length + 4)
    have hw_bound : 2 * ((n + edges'.length + 4) + 2) < 2 ^ w :=
      two_mul_lt_two_pow_wordSize (c := 3) (n := n + edges'.length + 4) (by omega)
    have h0_w : 0 < 2 ^ w := by omega
    have hw : 1 < 2 ^ w := by omega
    have hw2 : 2 < 2 ^ w := by omega
    have hw4 : 4 < 2 ^ w := by omega
    have hn_w : n < 2 ^ w := by omega
    have h2n_w : 2 * n < 2 ^ w := by omega
    have hm2_w : 2 + 2 * edges'.length < 2 ^ w := by omega
    let s₀ : State := {
      regs := fun r => if r = 14 then n else if r = 15 then 2 * n else if r = 16 then 4
        else if r = 17 then 0 else if r = 18 then 1 else 0
      arrs := fun a => if a = 0 then [n, edges'.length] ++ flatEdges edges'
        else if a = 9 then bitSetList omega.toFinset
        else if a = 11 then bitSetList (extNeighborhood C ({v} : Finset (Fin n)))
        else []
    }
    have hin₀ : s₀.arrs 0 = [n, edges'.length] ++ flatEdges edges' ++ [] := by
      simp [s₀]
    rcases Triple.parseGraphProg_spec (w := w) G' edges' [] 2 6 7 8 0 hedges'
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        hw2 hn_w hm2_w s₀ hin₀ with
      ⟨s₁, _, hex₁, _, _, _, _, hadj₁, hent₁, _⟩
    have hconst₁ : ConstRegs n 4 2 s₁ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hex₁.reg_eq_of_preservesReg (by decide)]; simp [s₀]
      · rw [hex₁.reg_eq_of_preservesReg (by decide)]; simp [s₀]
      · rw [hex₁.reg_eq_of_preservesReg (by decide)]; simp [s₀]
    have hS₁ : IsBitSet (extNeighborhood C ({v} : Finset (Fin n))) 11 s₁ := by
      refine IsBitSet.of_bitSetList _ 11 s₁ ?_
      rw [hex₁.arr_eq_of_preservesArr (by decide)]; simp [s₀]
    have hom₁ : IsBitSet omega.toFinset 9 s₁ := by
      refine IsBitSet.of_bitSetList _ 9 s₁ ?_
      rw [hex₁.arr_eq_of_preservesArr (by decide)]; simp [s₀]
    have hr17₁ : s₁.regs 17 = 0 := by
      rw [hex₁.reg_eq_of_preservesReg (by decide)]; simp [s₀]
    have hr18₁ : s₁.regs 18 = 1 := by
      rw [hex₁.reg_eq_of_preservesReg (by decide)]; simp [s₀]
    rcases initPathSystemRegProg_exec (w := w) G'
        (extNeighborhood C ({v} : Finset (Fin n))) omega.toFinset 18 2
        hw hn_w hconst₁ with
      ⟨s₂, _, _, _, hconst₂, hsys₂, hcard₂, harr₂, hreg₂⟩
    have hadj₂ : IsAdjList G' 6 7 8 (edgeNeighbors edges') s₂ :=
      hadj₁.of_arrs_eq (harr₂ 6 (by decide)) (harr₂ 7 (by decide)) (harr₂ 8 (by decide))
    have hent₂ : (s₂.arrs 8).length < 2 ^ w := by
      rw [harr₂ 8 (by decide), hent₁]; omega
    have hS₂ : IsBitSet (extNeighborhood C ({v} : Finset (Fin n))) 11 s₂ :=
      hS₁.of_arr_eq (harr₂ 11 (by decide))
    have hom₂ : IsBitSet omega.toFinset 9 s₂ :=
      hom₁.of_arr_eq (harr₂ 9 (by decide))
    have hr17₂ : s₂.regs 17 = 0 := by rw [hreg₂ 17 (by decide), hr17₁]
    have hr18₂ : s₂.regs 18 = 1 := by rw [hreg₂ 18 (by decide), hr18₁]
    rcases mengerLoopRegProg_exec (w := w) G' (edgeNeighbors edges')
        (extNeighborhood C ({v} : Finset (Fin n))) omega.toFinset
        6 7 8 11 9 18 2
        (by decide) (by decide) (by decide) (by decide) (by decide)
        hw h2n_w hw4 4 0 (by omega)
        hconst₂ hadj₂ hent₂ hS₂ hom₂ hsys₂ hcard₂ hr17₂ hr18₂ with
      ⟨s₃, _, _, _, _, _, _, hres₃⟩
    rcases hres₃ with ⟨_, used', pred', succ', hsys₃, hcard₃⟩ |
        ⟨_, used', pred', succ', items, hsys₃, hlt₃, _, hpar₃, hclosed₃, hinit₃, hnoZ₃⟩
    · exact ⟨fourLinkedPaths_of_menger hcore_adj hvZ hsys₃.1 hcard₃⟩
    · exfalso
      have hnot4 := (minOrderCoreSeparation_of_menger
        hcore_om hcore_adj hvZ hv_om hsys₃.1 (by omega) hinit₃ hclosed₃.to_closed hpar₃.2.1 hnoZ₃).2.1
      exact hnot4 h4

/-- Loop invariant for `alg83LoopProg` at vertex index `k ≤ x.n`. -/
def Alg83LoopInv (x : Alg81Input) (k : ℕ) (s : State) : Prop :=
  ∃ (Z : Finset (Fin x.n)) (C : SimpleGraph (Fin x.n)) (edges_C : List (Fin x.n × Fin x.n)),
    Alg83Trace x Z C ∧
    x.omega.toFinset ⊆ Z ∧
    (∀ u w : Fin x.n, C.Adj u w → u ∈ Z ∧ w ∈ Z) ∧
    (∀ u ∈ Z, u.1 < k → IsFourLinkedAt x.omega Z C u) ∧
    IsSimpleEdgeList C edges_C ∧
    edges_C.length ≤ (edgeListOf x.G).length + 3 * k ∧
    s.arrs 0 = [x.n, edges_C.length] ++ flatEdges edges_C ∧
    IsBitSet Z 14 s ∧
    IsBitSet x.omega.toFinset 9 s ∧
    ConstRegs x.n 4 2 s ∧
    s.regs 20 = k

theorem alg83ActiveVertexProg_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (C : SimpleGraph (Fin x.n))
    (edges_C : List (Fin x.n × Fin x.n)) (v : Fin x.n)
    (hw4 : 4 < 2 ^ w) (h2n_w : 2 * x.n < 2 ^ w)
    (hm8_w : 8 + 2 * edges_C.length < 2 ^ w)
    (htrace : Alg83Trace x Z C)
    (hom_sub : x.omega.toFinset ⊆ Z)
    (hadj_Z : ∀ a b : Fin x.n, C.Adj a b → a ∈ Z ∧ b ∈ Z)
    (hprev : ∀ u ∈ Z, u.1 < v.1 → IsFourLinkedAt x.omega Z C u)
    (hedges : IsSimpleEdgeList C edges_C)
    (hvZ : v ∈ Z) (hv_om : v ∉ x.omega.toFinset) {s : State}
    (hin : s.arrs 0 = [x.n, edges_C.length] ++ flatEdges edges_C)
    (hZ_bit : IsBitSet Z 14 s)
    (hom_bit : IsBitSet x.omega.toFinset 9 s)
    (hconst : ConstRegs x.n 4 2 s)
    (hr20 : s.regs 20 = v.1) :
    ∃ s' t Z' C' edges_C',
      Exec w alg83ActiveVertexProg s s' t ∧
      t ≤ 1290 * x.n + 520 * edges_C.length + 710 ∧
      Alg83Trace x Z' C' ∧
      x.omega.toFinset ⊆ Z' ∧
      (∀ a b : Fin x.n, C'.Adj a b → a ∈ Z' ∧ b ∈ Z') ∧
      (∀ u ∈ Z', u.1 < v.1 + 1 → IsFourLinkedAt x.omega Z' C' u) ∧
      IsSimpleEdgeList C' edges_C' ∧
      edges_C'.length ≤ edges_C.length + 3 ∧
      s'.arrs 0 = [x.n, edges_C'.length] ++ flatEdges edges_C' ∧
      IsBitSet Z' 14 s' ∧
      IsBitSet x.omega.toFinset 9 s' ∧
      ConstRegs x.n 4 2 s' ∧
      s'.regs 20 = v.1 ∧
      s'.arrs 1 = s.arrs 1 := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hm_w : edges_C.length < 2 ^ w := by omega
  have h2m_w : 2 * edges_C.length < 2 ^ w := by omega
  have hm2_w : 2 + 2 * edges_C.length < 2 ^ w := by omega
  -- 1. parseGraphProg 2 3 4 5 0
  have hin_extra : s.arrs 0 = [x.n, edges_C.length] ++ flatEdges edges_C ++ [] := by
    simpa using hin
  rcases Triple.parseGraphProg_spec (w := w) C edges_C [] 2 3 4 5 0 hedges
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw2 hn_w hm2_w s hin_extra with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, hr0₁, hr1₁, hadj₁, hent₁, _⟩
  dsimp only at ht₁
  rw [List.append_nil] at hin₁
  have hZ₁ : IsBitSet Z 14 s₁ :=
    hZ_bit.of_arr_eq (hex₁.arr_eq_of_preservesArr (by decide))
  have hom₁ : IsBitSet x.omega.toFinset 9 s₁ :=
    hom_bit.of_arr_eq (hex₁.arr_eq_of_preservesArr (by decide))
  have hconst₁ : ConstRegs x.n 4 2 s₁ :=
    hconst.of_regs_eq
      (hex₁.reg_eq_of_preservesReg (by decide))
      (hex₁.reg_eq_of_preservesReg (by decide))
      (hex₁.reg_eq_of_preservesReg (by decide))
  have hr20₁ : s₁.regs 20 = v.1 := by
    rw [hex₁.reg_eq_of_preservesReg (by decide), hr20]
  -- 2. alg83SingletonProg 15 14 20
  rcases alg83SingletonProg_exec v 15 14 20 hw hn_w hconst₁.1 hr20₁ with
    ⟨s₂, t₂, hex₂, ht₂, hv_bit₂, harr₂, hreg₂⟩
  have hadj₂ : IsAdjList C 3 4 5 (edgeNeighbors edges_C) s₂ :=
    hadj₁.of_arrs_eq (harr₂ 3 (by decide)) (harr₂ 4 (by decide)) (harr₂ 5 (by decide))
  have hent₂ : (s₂.arrs 5).length < 2 ^ w := by
    rw [harr₂ 5 (by decide), hent₁]; exact h2m_w
  have hconst₂ : ConstRegs x.n 4 2 s₂ :=
    hconst₁.of_regs_eq (congrFun hreg₂ 14) (congrFun hreg₂ 15) (congrFun hreg₂ 16)
  -- 3. buildComplAndExtNhdProg 3 4 5 15 10 11
  have htot_C : totalAdjEntries (edgeNeighbors edges_C) = 2 * edges_C.length :=
    totalAdjEntries_edgeNeighbors edges_C hedges.1
  rcases buildComplAndExtNhdProg_exec C (edgeNeighbors edges_C) ({v} : Finset (Fin x.n))
      3 4 5 15 10 11
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hw hn_w hadj₂ hent₂ hv_bit₂ hconst₂.1 with
    ⟨s₃, t₃, hex₃, ht₃, hY₃, hS₃, harr₃, hreg₃⟩
  rw [htot_C] at ht₃
  have hr1_₃ : s₃.regs 1 = edges_C.length := by
    rw [hreg₃ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        congrFun hreg₂ 1, hr1₁]
  -- 4. r_19 := 2 * r_1, restrictGraphProg 3 4 5 10 6 7 8 14 19 2 3 4 5 6 7 8
  let s₄ := s₃.setReg 19 (2 * edges_C.length)
  have hex₄ : Exec w (.assign 19 (.op .mul (.const 2) (.reg 1))) s₃ s₄ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_₃, hw2, hm_w, h2m_w])
  have hadj₄ : IsAdjList C 3 4 5 (edgeNeighbors edges_C) s₄ :=
    hadj₂.of_arrs_eq (harr₃ 3 (by decide) (by decide))
      (harr₃ 4 (by decide) (by decide)) (harr₃ 5 (by decide) (by decide))
  have hent₄ : (s₄.arrs 5).length < 2 ^ w := by
    simp [s₄, harr₃ 5 (by decide) (by decide), hent₂]
  have hconst₄ : ConstRegs x.n 4 2 s₄ :=
    hconst₂.of_regs_eq
      (by simp [s₄, State.setReg, hreg₃ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₄, State.setReg, hreg₃ 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₄, State.setReg, hreg₃ 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
  have hcards_le : (edgesInSet C (Finset.univ \ ({v} : Finset (Fin x.n)))).card ≤ edges_C.length := by
    classical
    have hcard_C : C.edgeFinset.card = edges_C.length := by
      have h1 := totalAdjEntries_eq_two_mul_card_edgeFinset hadj₁.2
      omega
    rw [← hcard_C]
    exact card_edgesInSet_le_card_edgeFinset C _
  let _ : DecidableRel C.Adj := Classical.decRel C.Adj
  rcases restrictGraphProg_exec C (edgeNeighbors edges_C) (Finset.univ \ ({v} : Finset (Fin x.n)))
      (2 * edges_C.length) 3 4 5 10 6 7 8 14 19 2 3 4 5 6 7 8
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn_w h2m_w (by omega) hadj₄ hent₄ (hY₃.of_arr_eq rfl) hconst₄.1 (by simp [s₄]) with
    ⟨s₅, t₅, hex₅, ht₅, hadj_r₅, hent_r₅, _, harr₅, hreg₅⟩
  rw [htot_C] at ht₅
  -- 5. r_17 := 0, r_18 := 1, initPathSystemRegProg 18 2, mengerLoopRegProg 6 7 8 11 9 18 2
  let s₆ := s₅.setReg 17 0
  have hex₆ : Exec w (.assign 17 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₇ := s₆.setReg 18 1
  have hex₇ : Exec w (.assign 18 (.const 1)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hconst₇ : ConstRegs x.n 4 2 s₇ :=
    hconst₄.of_regs_eq
      (by simp [s₇, s₆, State.setReg, hreg₅ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₇, s₆, State.setReg, hreg₅ 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₇, s₆, State.setReg, hreg₅ 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
  rcases initPathSystemRegProg_exec (w := w)
      (restrictGraph C (Finset.univ \ ({v} : Finset (Fin x.n))))
      (extNeighborhood C ({v} : Finset (Fin x.n))) x.omega.toFinset 18 2
      hw hn_w hconst₇ with
    ⟨s₈, t₈, hex₈, ht₈, hconst₈, hsys₈, hcard₈, harr₈, hreg₈⟩
  have harr₈_lt : ∀ a < 18, s₈.arrs a = s₅.arrs a := by
    intro a ha; rw [harr₈ a ha]; rfl
  have hadj_r₈ : IsAdjList (restrictGraph C (Finset.univ \ ({v} : Finset (Fin x.n))))
      6 7 8 (restrictListFamily (Finset.univ \ ({v} : Finset (Fin x.n))) (edgeNeighbors edges_C)) s₈ :=
    hadj_r₅.of_arrs_eq (harr₈_lt 6 (by decide)) (harr₈_lt 7 (by decide)) (harr₈_lt 8 (by decide))
  have hent_r₈ : (s₈.arrs 8).length < 2 ^ w := by
    rw [harr₈_lt 8 (by decide), hent_r₅]; exact h2m_w
  have hS₈ : IsBitSet (extNeighborhood C ({v} : Finset (Fin x.n))) 11 s₈ :=
    hS₃.of_arr_eq (by rw [harr₈_lt 11 (by decide), harr₅ 11 (by decide) (by decide) (by decide)]; rfl)
  have hom₈ : IsBitSet x.omega.toFinset 9 s₈ :=
    hom₁.of_arr_eq (by
      rw [harr₈_lt 9 (by decide), harr₅ 9 (by decide) (by decide) (by decide)]
      change s₃.arrs 9 = s₁.arrs 9
      rw [harr₃ 9 (by decide) (by decide), harr₂ 9 (by decide)])
  have hr17_₈ : s₈.regs 17 = 0 := by
    rw [hreg₈ 17 (by decide)]; simp [s₇, s₆, State.setReg]
  have hr18_₈ : s₈.regs 18 = 1 := by
    rw [hreg₈ 18 (by decide)]; simp [s₇]
  rcases mengerLoopRegProg_exec (w := w)
      (restrictGraph C (Finset.univ \ ({v} : Finset (Fin x.n))))
      (restrictListFamily (Finset.univ \ ({v} : Finset (Fin x.n))) (edgeNeighbors edges_C))
      (extNeighborhood C ({v} : Finset (Fin x.n))) x.omega.toFinset
      6 7 8 11 9 18 2
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw h2n_w hw4 4 0 (by omega)
      hconst₈ hadj_r₈ hent_r₈ hS₈ hom₈ hsys₈ hcard₈ hr17_₈ hr18_₈ with
    ⟨s₉, t₉, hex₉, ht₉, hconst₉, harr₉, hreg₉, hres₉⟩
  have htot_r :
      totalAdjEntries (restrictListFamily (Finset.univ \ ({v} : Finset (Fin x.n))) (edgeNeighbors edges_C)) ≤
        2 * edges_C.length := by
    classical
    have hcard_C : C.edgeFinset.card = edges_C.length := by
      have h1 := totalAdjEntries_eq_two_mul_card_edgeFinset hadj₁.2
      omega
    rw [totalAdjEntries_eq_two_mul_card_edgeFinset hadj_r₅.2, card_edgeFinset_restrictGraph]
    omega
  have ht₉_le : t₉ ≤ 3 + 4 * (65 + 264 * x.n + 62 * edges_C.length) := by
    have hinner :
        65 + 264 * x.n + 31 * totalAdjEntries (restrictListFamily (Finset.univ \ ({v} : Finset (Fin x.n))) (edgeNeighbors edges_C)) ≤
          65 + 264 * x.n + 62 * edges_C.length := by omega
    have hmul := Nat.mul_le_mul_left 4 hinner
    omega
  have hin₉ : s₉.arrs 0 = [x.n, edges_C.length] ++ flatEdges edges_C := by
    rw [harr₉ 0 (by decide), harr₈_lt 0 (by decide), harr₅ 0 (by decide) (by decide) (by decide)]
    change s₃.arrs 0 = _
    rw [harr₃ 0 (by decide) (by decide), harr₂ 0 (by decide), hin₁]
  have hZ₉ : IsBitSet Z 14 s₉ :=
    hZ₁.of_arr_eq (by
      rw [harr₉ 14 (by decide), harr₈_lt 14 (by decide), harr₅ 14 (by decide) (by decide) (by decide)]
      change s₃.arrs 14 = s₁.arrs 14
      rw [harr₃ 14 (by decide) (by decide), harr₂ 14 (by decide)])
  have hom₉ : IsBitSet x.omega.toFinset 9 s₉ :=
    hom₈.of_arr_eq (harr₉ 9 (by decide))
  have hv_bit₉ : IsBitSet ({v} : Finset (Fin x.n)) 15 s₉ :=
    hv_bit₂.of_arr_eq (by
      rw [harr₉ 15 (by decide), harr₈_lt 15 (by decide), harr₅ 15 (by decide) (by decide) (by decide)]
      change s₃.arrs 15 = s₂.arrs 15
      rw [harr₃ 15 (by decide) (by decide)])
  have hr20_₉ : s₉.regs 20 = v.1 := by
    rw [hreg₉ 20 (by decide), hreg₈ 20 (by decide)]
    simp only [s₇, s₆, State.setReg_regs_ne _ _ (by decide : (20 : Reg) ≠ 18),
      State.setReg_regs_ne _ _ (by decide : (20 : Reg) ≠ 17)]
    rw [hreg₅ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s₄, State.setReg_regs_ne _ _ (by decide : (20 : Reg) ≠ 19)]
    rw [hreg₃ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      congrFun hreg₂ 20, hr20₁]
  have harr1_₉ : s₉.arrs 1 = s.arrs 1 := by
    rw [harr₉ 1 (by decide), harr₈_lt 1 (by decide), harr₅ 1 (by decide) (by decide) (by decide)]
    change s₃.arrs 1 = s.arrs 1
    rw [harr₃ 1 (by decide) (by decide), harr₂ 1 (by decide),
        hex₁.arr_eq_of_preservesArr (by decide)]
  -- 6. Branch on s₉.regs 18 (`hres₉`)
  rcases hres₉ with ⟨hr18_₉, used', pred', succ', hsys₉, hcard₉⟩ |
      ⟨hr18_₉, used', pred', succ', items, hsys₉, hlt₉, hvis₉, hpar₉, hclosed₉, hinit₉, hnoZ₉⟩
  · -- Case 1: 4 paths found (`s₉.regs 18 = 1`)
    have hcond18 : (Expr.reg 18).eval w s₉ = some 1 := by
      simp [Expr.eval, checkWord, hr18_₉, hw]
    have hpaths : FourLinkedPaths x.omega Z C v :=
      fourLinkedPaths_of_menger hadj_Z hvZ hsys₉.1 hcard₉
    have h4_v : IsFourLinkedAt x.omega Z C v :=
      isFourLinkedAt_of_fourLinkedPaths hpaths
    refine ⟨s₉, t₁ + (t₂ + (t₃ + (4 + (t₅ + (2 + (2 + (t₈ + (t₉ + (1 + 1))))))))),
      Z, C, edges_C,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
        (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.ite_true hcond18 (by decide) (.skip s₉)))))))))),
      by linarith [ht₁, ht₂, ht₃, ht₅, ht₈, ht₉_le], htrace, hom_sub, hadj_Z, ?_, hedges, by omega,
      hin₉, hZ₉, hom₉, hconst₉, hr20_₉, harr1_₉⟩
    intro u huZ hu_lt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hu_lt with hlt | heq
    · exact hprev u huZ hlt
    · have huv : u = v := Fin.ext heq
      subst huv
      exact h4_v
  · -- Case 2: `< 4` paths found (`s₉.regs 18 = 0`)
    have hcond18 : (Expr.reg 18).eval w s₉ = some 0 := by
      simp [Expr.eval, checkWord, hr18_₉, h0_w]
    obtain ⟨hmin_sep, hnot4_v, _⟩ :=
      minOrderCoreSeparation_of_menger hom_sub hadj_Z hvZ hv_om
        hsys₉.1 (by omega) hinit₉ hclosed₉.to_closed hpar₉.2.1 hnoZ₉
    let A := Z ∩ alg62VB ({v} : Finset (Fin x.n)) items
    let B := Z ∩ alg62VA ({v} : Finset (Fin x.n)) items
    let C' := coreStepGraph C A B
    let edges_C' := coreStepEdges A B edges_C
    -- 6a. buildCandSepProg 15 21 12 13
    rcases buildCandSepProg_exec ({v} : Finset (Fin x.n)) items 15 21 12 13
        (by decide) (by decide) (by decide) (by decide) (by decide)
        hw h2n_w hv_bit₉ hvis₉ hconst₉.1 with
      ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hVA₁₀, hVB₁₀, _, _, harr₁₀, hreg₁₀⟩
    have hin₁₀ : s₁₀.arrs 0 = [x.n, edges_C.length] ++ flatEdges edges_C := by
      rw [harr₁₀ 0 (by decide) (by decide), hin₉]
    have hZ₁₀ : IsBitSet Z 14 s₁₀ :=
      hZ₉.of_arr_eq (harr₁₀ 14 (by decide) (by decide))
    have hconst₁₀ : ConstRegs x.n 4 2 s₁₀ :=
      hconst₉.of_regs_eq
        (hreg₁₀ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hreg₁₀ 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hreg₁₀ 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    -- 6b. updateCoreGraphProg
    rcases updateCoreGraphProg_exec Z (alg62VA ({v} : Finset (Fin x.n)) items)
        (alg62VB ({v} : Finset (Fin x.n)) items) edges_C
        hw3 hn_w hm8_w hin₁₀ hZ₁₀ hVA₁₀ hVB₁₀ hconst₁₀.1 with
      ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hB₁₁, hin₁₁, _, harr₁₁, hreg₁₁⟩
    have hom₁₁ : IsBitSet x.omega.toFinset 9 s₁₁ :=
      hom₉.of_arr_eq (by
        rw [harr₁₁ 9 (by decide) (by decide) (by decide) (by decide),
            harr₁₀ 9 (by decide) (by decide)])
    have hconst₁₁ : ConstRegs x.n 4 2 s₁₁ :=
      hconst₁₀.of_regs_eq
        (hreg₁₁ 14 (by decide) (by decide))
        (hreg₁₁ 15 (by decide) (by decide))
        (hreg₁₁ 16 (by decide) (by decide))
    have hr20_₁₁ : s₁₁.regs 20 = v.1 := by
      rw [hreg₁₁ 20 (by decide) (by decide),
          hreg₁₀ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hr20_₉]
    have harr1_₁₁ : s₁₁.arrs 1 = s.arrs 1 := by
      rw [harr₁₁ 1 (by decide) (by decide) (by decide) (by decide),
          harr₁₀ 1 (by decide) (by decide), harr1_₉]
    have htrace' : Alg83Trace x B C' :=
      .step v A B htrace hvZ hnot4_v hmin_sep
    have hom_sub' : x.omega.toFinset ⊆ B := hmin_sep.2.2.1
    have hadj_B : ∀ a b : Fin x.n, C'.Adj a b → a ∈ B ∧ b ∈ B := by
      intro a b hadj
      exact coreStepGraph_adj_mem hadj
    have hprev' : ∀ u ∈ B, u.1 < v.1 + 1 → IsFourLinkedAt x.omega B C' u := by
      intro u huB hu_lt
      have hv_not_B : v ∉ B := (Finset.mem_sdiff.mp hmin_sep.2.1).2
      have huv_ne : u ≠ v := fun heq => hv_not_B (heq ▸ huB)
      have hu_lt_v : u.1 < v.1 := by
        have : u.1 ≠ v.1 := fun h => huv_ne (Fin.ext h)
        omega
      have huZ : u ∈ Z := hmin_sep.1.2.1 huB
      exact isFourLinkedAt_coreStepGraph hmin_sep.1 (hprev u huZ hu_lt_v)
    have hedges' : IsSimpleEdgeList C' edges_C' :=
      isSimpleEdgeList_coreStepEdges hedges hmin_sep.2.2.2.1
    have hlen' : edges_C'.length ≤ edges_C.length + 3 :=
      length_coreStepEdges_le A B edges_C
    refine ⟨s₁₁, t₁ + (t₂ + (t₃ + (4 + (t₅ + (2 + (2 + (t₈ + (t₉ + (1 + (t₁₀ + t₁₁)))))))))),
      B, C', edges_C',
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
        (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉
          (.ite_false hcond18 (.seq hex₁₀ hex₁₁)))))))))),
      by linarith [ht₁, ht₂, ht₃, ht₅, ht₈, ht₉_le, ht₁₀, ht₁₁],
      htrace', hom_sub', hadj_B, hprev', hedges', hlen',
      hin₁₁, hB₁₁, hom₁₁, hconst₁₁, hr20_₁₁, harr1_₁₁⟩

theorem alg83VertexStepProg_exec {w : ℕ} (x : Alg81Input) (k : ℕ) (hk : k < x.n)
    (hw4 : 4 < 2 ^ w) (h2n_w : 2 * x.n < 2 ^ w)
    (hm_max_w : 8 + 2 * ((edgeListOf x.G).length + 3 * x.n) < 2 ^ w) {s : State}
    (hinv : Alg83LoopInv x k s) :
    ∃ s' t,
      Exec w alg83VertexStepProg s s' t ∧
      t ≤ 2850 * x.n + 520 * (edgeListOf x.G).length + 730 ∧
      Alg83LoopInv x (k + 1) (s'.setReg 20 (k + 1)) ∧
      s'.regs 20 = k ∧
      s'.arrs 1 = s.arrs 1 := by
  rcases hinv with ⟨Z, C, edges_C, htrace, hom_sub, hadj_Z, hprev,
    hedges, hlen_edges, hin, hZ_bit, hom_bit, hconst, hr20⟩
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  have hm8_w : 8 + 2 * edges_C.length < 2 ^ w := by omega
  let v : Fin x.n := ⟨k, hk⟩
  -- 1. r_2 := a_Z[r_20], r_3 := a_omega[r_20], r_2 := r_2 - r_3
  have hk_Z : k < (s.arrs 14).length := by rw [hZ_bit.1]; exact hk
  have hval_Z : (s.arrs 14)[k]'hk_Z = if v ∈ Z then 1 else 0 := hZ_bit.getElem_eq_ite v
  have hbZ_w : (if v ∈ Z then 1 else 0) < 2 ^ w := by split_ifs <;> omega
  let s₁ := s.setReg 2 (if v ∈ Z then 1 else 0)
  have hex₁ : Exec w (.assign 2 (.read 14 (.reg 20))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hr20, hk_w, hk_Z, hval_Z, hbZ_w])
  have hk_om : k < (s.arrs 9).length := by rw [hom_bit.1]; exact hk
  have hval_om : (s.arrs 9)[k]'hk_om = if v ∈ x.omega then 1 else 0 := by
    simpa using hom_bit.getElem_eq_ite v
  have hbom_w : (if v ∈ x.omega then 1 else 0) < 2 ^ w := by split_ifs <;> omega
  let s₂ := s₁.setReg 3 (if v ∈ x.omega.toFinset then 1 else 0)
  have hex₂ : Exec w (.assign 3 (.read 9 (.reg 20))) s₁ s₂ 3 :=
    .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hr20, hk_w, hk_om, hval_om, hbom_w])
  let diff := (if v ∈ Z then 1 else 0) - (if v ∈ x.omega.toFinset then 1 else 0)
  have hdiff_w' : (if v ∈ Z then 1 else 0) - (if v ∈ x.omega then 1 else 0) < 2 ^ w := by
    split_ifs <;> omega
  let s₃ := s₂.setReg 2 diff
  have hex₃ : Exec w (.assign 2 (.op .sub (.reg 2) (.reg 3))) s₂ s₃ 4 :=
    .assign (by simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hbZ_w, hbom_w, diff, hdiff_w'])
  have hconst₃ : ConstRegs x.n 4 2 s₃ :=
    hconst.of_regs_eq (by simp [s₃, s₂, s₁, State.setReg])
      (by simp [s₃, s₂, s₁, State.setReg]) (by simp [s₃, s₂, s₁, State.setReg])
  have hr20_₃ : s₃.regs 20 = k := by simp [s₃, s₂, s₁, State.setReg, hr20]
  by_cases hv_act : v ∈ Z ∧ v ∉ x.omega.toFinset
  · have hdiff_eq : diff = 1 := by simp only [diff, hv_act.1, hv_act.2, ite_true, ite_false]
    have hcond : (Expr.reg 2).eval w s₃ = some 1 := by
      simp [ s₃, Expr.eval, checkWord, hdiff_eq, hw]
    rcases alg83ActiveVertexProg_exec x Z C edges_C v hw4 h2n_w hm8_w
        htrace hom_sub hadj_Z hprev hedges hv_act.1 hv_act.2 (s := s₃)
        hin
        (hZ_bit.of_arr_eq rfl) (hom_bit.of_arr_eq rfl) hconst₃ hr20_₃ with
      ⟨s₄, t₄, Z', C', edges_C', hex₄, ht₄, htrace', hom_sub', hadj_Z', hprev',
        hedges', hlen', hin₄, hZ₄, hom₄, hconst₄, hr20_₄, harr1_₄⟩
    have hk_le_n : k ≤ x.n := by omega
    have htime : 3 + (3 + (4 + (1 + t₄))) ≤ 2850 * x.n + 520 * (edgeListOf x.G).length + 730 := by
      linarith [ht₄, hlen_edges, hk_le_n]
    refine ⟨s₄, 3 + (3 + (4 + (1 + t₄))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.ite_true hcond (by decide) hex₄))),
      htime, ?_, hr20_₄, harr1_₄⟩
    refine ⟨Z', C', edges_C', htrace', hom_sub', hadj_Z', hprev', hedges',
      by omega, hin₄, hZ₄.of_arr_eq rfl, hom₄.of_arr_eq rfl,
      hconst₄.of_regs_eq (by simp [State.setReg]) (by simp [State.setReg]) (by simp [State.setReg]),
      by simp [State.setReg]⟩
  · have hdiff_eq : diff = 0 := by
      dsimp [diff]
      by_cases hvZ : v ∈ Z
      · have hv_om : v ∈ x.omega.toFinset := by tauto
        simp [hvZ, hv_om]
      · simp [hvZ]
    have hcond : (Expr.reg 2).eval w s₃ = some 0 := by
      simp [s₃, Expr.eval, checkWord, hdiff_eq, h0_w]
    refine ⟨s₃, 3 + (3 + (4 + (1 + 1))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.ite_false hcond (.skip s₃)))),
      by omega, ?_, hr20_₃, rfl⟩
    refine ⟨Z, C, edges_C, htrace, hom_sub, hadj_Z, ?_, hedges,
      by omega, by simp [s₃, s₂, s₁, hin], hZ_bit.of_arr_eq rfl, hom_bit.of_arr_eq rfl,
      hconst₃.of_regs_eq (by simp [State.setReg]) (by simp [State.setReg]) (by simp [State.setReg]),
      by simp [State.setReg]⟩
    intro u huZ hu_lt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hu_lt with hlt | heq
    · exact hprev u huZ hlt
    · have huv : u = v := Fin.ext heq
      have hvZ : v ∈ Z := huv ▸ huZ
      have hu_om : u ∈ x.omega.toFinset := by
        rw [huv]
        tauto
      exact isFourLinkedAt_of_fourLinkedPaths
        (fourLinkedPaths_of_mem_omega (omega := x.omega) (Z := Z) (C := C) huZ hu_om)

theorem alg83Loop_aux {w : ℕ} (x : Alg81Input)
    (hw4 : 4 < 2 ^ w) (h2n_w : 2 * x.n < 2 ^ w)
    (hm_max_w : 8 + 2 * ((edgeListOf x.G).length + 3 * x.n) < 2 ^ w) :
    ∀ rem k (_hrem : k + rem = x.n) {s : State}
      (_hinv : Alg83LoopInv x k s),
      ∃ s' t,
        Exec w (forUp 20 (.reg 14) alg83VertexStepProg) s s' t ∧
        t ≤ rem * (2850 * x.n + 520 * (edgeListOf x.G).length + 737) + 3 ∧
        Alg83LoopInv x x.n s' ∧
        s'.arrs 1 = s.arrs 1
  | 0, k, _hrem, s, hinv => by
    have hk_eq : k = x.n := by omega
    subst hk_eq
    have h0_w : 0 < 2 ^ w := by omega
    have hn_w : x.n < 2 ^ w := by omega
    rcases hinv with ⟨Z, C, edges_C, htrace, hom_sub, hadj_Z, hprev,
      hedges, hlen_edges, hin, hZ_bit, hom_bit, hconst, hr20⟩
    have hcond : (Expr.op .lt (.reg 20) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20, hconst.1, hn_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega,
      ⟨Z, C, edges_C, htrace, hom_sub, hadj_Z, hprev, hedges, hlen_edges,
        hin, hZ_bit, hom_bit, hconst, hr20⟩, rfl⟩
  | rem + 1, k, _hrem, s, hinv => by
    have hk_lt : k < x.n := by omega
    have hw : 1 < 2 ^ w := by omega
    have hn_w : x.n < 2 ^ w := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 20) (.reg 14)).eval w s = some 1 := by
      rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hconst, hr20⟩
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20, hconst.1, hk_w, hn_w, hk_lt, hw]
    rcases alg83VertexStepProg_exec x k hk_lt hw4 h2n_w hm_max_w hinv with
      ⟨s₁, t₁, hex₁, ht₁, hinv₁, hr20₁, harr1₁⟩
    let s₂ := s₁.setReg 20 (k + 1)
    have hex_inc : Exec w (.assign 20 (.op .add (.reg 20) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20₁, hk_w, hw,
        show k + 1 < 2 ^ w by omega])
    rcases alg83Loop_aux x hw4 h2n_w hm_max_w rem (k + 1) (by omega) hinv₁ with
      ⟨s₃, t₃, hex₃, ht₃, hinv₃, harr1₃⟩
    have hmul : (rem + 1) * (2850 * x.n + 520 * (edgeListOf x.G).length + 737) =
        (2850 * x.n + 520 * (edgeListOf x.G).length + 737) +
          rem * (2850 * x.n + 520 * (edgeListOf x.G).length + 737) := by
      ring
    refine ⟨s₃, 3 + (t₁ + 4) + t₃,
      .while_true hcond (by omega) (.seq hex₁ hex_inc) hex₃,
      by linarith [ht₁, ht₃, hmul], hinv₃, by rw [harr1₃]; exact harr1₁⟩

theorem alg83LoopProg_exec {w : ℕ} (x : Alg81Input)
    (hw4 : 4 < 2 ^ w) (h2n_w : 2 * x.n < 2 ^ w)
    (hm_max_w : 8 + 2 * ((edgeListOf x.G).length + 3 * x.n) < 2 ^ w) {s : State}
    (hin : s.arrs 0 = [x.n, (edgeListOf x.G).length] ++ flatEdges (edgeListOf x.G))
    (hom_bit : IsBitSet x.omega.toFinset 9 s)
    (hZ_bit : IsBitSet (Finset.univ : Finset (Fin x.n)) 14 s)
    (hconst : ConstRegs x.n 4 2 s) :
    ∃ s' t,
      Exec w alg83LoopProg s s' t ∧
      t ≤ x.n * (2850 * x.n + 520 * (edgeListOf x.G).length + 737) + 5 ∧
      Alg83LoopInv x x.n s' ∧
      s'.arrs 1 = s.arrs 1 := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 20 0
  have hex₁ : Exec w (.assign 20 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hinv₁ : Alg83LoopInv x 0 s₁ := by
    refine ⟨Finset.univ, x.G, edgeListOf x.G, .refl, Finset.subset_univ _,
      fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      fun _ _ hlt => by omega,
      isSimpleEdgeList_edgeListOf x.G, by omega,
      by simp [s₁, hin],
      hZ_bit.of_arr_eq rfl, hom_bit.of_arr_eq rfl,
      hconst.of_regs_eq (by simp [s₁, State.setReg])
        (by simp [s₁, State.setReg]) (by simp [s₁, State.setReg]),
      by simp [s₁]⟩
  rcases alg83Loop_aux x hw4 h2n_w hm_max_w x.n 0 (by omega) hinv₁ with
    ⟨s₂, t₂, hex₂, ht₂, hinv₂, harr1₂⟩
  exact ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hinv₂, harr1₂⟩

/-! ## Section 4: Output Serialization, Decoding, and `gm13_algorithm_8_3` -/

/-- Reconstruct a `SimpleGraph (Fin n)` from a flat edge encoding
`l = [n, m, u_0, v_0, ..., u_{m-1}, v_{m-1}]`. -/
def graphOfFlatEdges (n : ℕ) (l : List ℕ) : SimpleGraph (Fin n) where
  Adj u v :=
    u ≠ v ∧
    ∃ k < l.getD 1 0,
      (l.getD (2 + 2 * k) 0 = u.1 ∧ l.getD (2 + 2 * k + 1) 0 = v.1) ∨
      (l.getD (2 + 2 * k) 0 = v.1 ∧ l.getD (2 + 2 * k + 1) 0 = u.1)
  symm := ⟨fun _ _ h => ⟨h.1.symm, let ⟨k, hk, hpair⟩ := h.2; ⟨k, hk, hpair.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem graphOfFlatEdges_eq {n : ℕ} (C : SimpleGraph (Fin n)) (edges : List (Fin n × Fin n))
    (hedges : IsSimpleEdgeList C edges) :
    graphOfFlatEdges n ([n, edges.length] ++ flatEdges edges) = C := by
  let l := [n, edges.length] ++ flatEdges edges
  have hm : l.getD 1 0 = edges.length := by simp [l]
  have heven : ∀ k (hk : k < edges.length), l.getD (2 + 2 * k) 0 = (edges[k]'hk).1.1 := by
    intro k hk
    have hidx : 2 + 2 * k < l.length := by simp [l, length_flatEdges]; omega
    have h2 : 2 + 2 * k = (2 * k) + 1 + 1 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
    simp only [l, h2, List.cons_append, List.nil_append, List.getElem_cons_succ]
    exact getElem_flatEdges_even edges hk
  have hodd : ∀ k (hk : k < edges.length), l.getD (2 + 2 * k + 1) 0 = (edges[k]'hk).2.1 := by
    intro k hk
    have hidx : 2 + 2 * k + 1 < l.length := by simp [l, length_flatEdges]; omega
    have h2 : 2 + 2 * k + 1 = (2 * k + 1) + 1 + 1 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
    simp only [l, h2, List.cons_append, List.nil_append, List.getElem_cons_succ]
    exact getElem_flatEdges_odd edges hk
  ext u v
  change (graphOfFlatEdges n l).Adj u v ↔ C.Adj u v
  dsimp [graphOfFlatEdges]
  rw [hm, hedges.2.2 u v]
  constructor
  · rintro ⟨_, k, hk, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · rw [heven k hk] at h1
      rw [hodd k hk] at h2
      exact ⟨k, hk, Or.inl ⟨Fin.ext h1, Fin.ext h2⟩⟩
    · rw [heven k hk] at h1
      rw [hodd k hk] at h2
      exact ⟨k, hk, Or.inr ⟨Fin.ext h1, Fin.ext h2⟩⟩
  · rintro ⟨k, hk, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · refine ⟨hedges.1 k hk, k, hk, Or.inl ⟨heven k hk, hodd k hk⟩⟩
    · refine ⟨(hedges.1 k hk).symm, k, hk, Or.inr ⟨heven k hk, hodd k hk⟩⟩

/-- Output of GM XIII Algorithm (8.3) on input society `x : Alg81Input`:
the vertex set `Z = V(C)` and graph `C` of the 4-linked core. -/
structure Alg83Output (x : Alg81Input) where
  /-- Vertex set `V(C) ⊆ V(G)` of the output 4-linked core. -/
  Z : Finset (Fin x.n)
  /-- Graph `C` of the output 4-linked core. -/
  C : SimpleGraph (Fin x.n)

/-- Convert an `Alg83Output x` into a `Graph (Fin x.n) (Sym2 (Fin x.n))` on vertex set `out.Z`. -/
def Alg83Output.toCoreGraph {x : Alg81Input} (out : Alg83Output x) :
    Graph (Fin x.n) (Sym2 (Fin x.n)) :=
  Compute.toCoreGraph out.Z out.C

/-- Pure decoder reconstructing `Alg83Output x` from
`outArr = bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C)`. -/
def decAlg83Out (x : Alg81Input) (out : List ℕ) : Alg83Output x where
  Z := finsetOfBitList x.n (out.take x.n)
  C := graphOfFlatEdges x.n (out.drop x.n)

theorem decAlg83Out_eq (x : Alg81Input) (Z : Finset (Fin x.n)) (C : SimpleGraph (Fin x.n))
    (edges : List (Fin x.n × Fin x.n)) (hedges : IsSimpleEdgeList C edges) :
    decAlg83Out x (bitSetList Z ++ ([x.n, edges.length] ++ flatEdges edges)) = ⟨Z, C⟩ := by
  have htake :
      (bitSetList Z ++ ([x.n, edges.length] ++ flatEdges edges)).take x.n = bitSetList Z :=
    List.take_left' (length_bitSetList Z)
  have hdrop :
      (bitSetList Z ++ ([x.n, edges.length] ++ flatEdges edges)).drop x.n =
        [x.n, edges.length] ++ flatEdges edges :=
    List.drop_left' (length_bitSetList Z)
  unfold decAlg83Out
  rw [htake, hdrop, finsetOfBitList_bitSetList, graphOfFlatEdges_eq C edges hedges]

/-- Output validity predicate for GM XIII Algorithm (8.3) (pages 93–95):
1. `out.toCoreGraph` is a core of `x.toSociety` (`GM13.IsCoreOf x.toSociety out.toCoreGraph`).
2. `out.toCoreGraph` is a 4-linked core of `x.toSociety`
   (`GM13.IsFourLinkedCore x.toSociety out.toCoreGraph`).
3. `(out.Z, out.C)` is obtained from `(Finset.univ, x.G)` by a valid sequence of (8.2) core steps
   (`Alg83Trace x out.Z out.C`).
4. `Ω ⊆ out.Z` and every edge of `out.C` has both endpoints in `out.Z`.
5. `(out.Z, out.C)` satisfies `IsFourLinkedCore x.omega out.Z out.C`.
6. Every vertex `v ∈ out.Z` has four `({v}, Ω)`-paths in `out.C` that are pairwise vertex-disjoint
   except at `v` (`FourLinkedPaths x.omega out.Z out.C v`). -/
def IsValidAlg83Output (x : Alg81Input) (out : Alg83Output x) : Prop :=
  GM13.IsCoreOf x.toSociety out.toCoreGraph ∧
  GM13.IsFourLinkedCore x.toSociety out.toCoreGraph ∧
  Alg83Trace x out.Z out.C ∧
  x.omega.toFinset ⊆ out.Z ∧
  (∀ u w : Fin x.n, out.C.Adj u w → u ∈ out.Z ∧ w ∈ out.Z) ∧
  IsFourLinkedCore x.omega out.Z out.C ∧
  ∀ v ∈ out.Z, Nonempty (FourLinkedPaths x.omega out.Z out.C v)

/-- Program that writes `bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C)` to
`outArr = 1`, preserving `inArr = 0`, `a_Z = 14`, `a_omega = 9`, and `ConstRegs x.n 4 2`. -/
def alg83WriteOutProg : Cmd :=
  .seq (.assign 1 (.read 0 (.const 1)))
    (.seq (.assign 20 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))))
      (.seq (.assign 21 (.op .add (.reg 14) (.reg 20)))
        (.seq (.alloc outArr (.reg 21))
          (.seq (copyToOutProg 14 (.const 0) 2)
            (.seq (.assign 22 (.reg 14))
              (.seq (.assign 14 (.reg 20))
                (.seq (.assign 15 (.op .mul (.const 2) (.reg 14)))
                  (.seq (.assign 16 (.const 0))
                    (.seq (copyToOutProg 0 (.reg 22) 2)
                      (.seq (.assign 14 (.reg 22))
                        (.seq (.assign 15 (.op .mul (.const 2) (.reg 14)))
                          (.assign 16 (.const 4)))))))))))))

theorem alg83WriteOutProg_exec {w n : ℕ} (Z : Finset (Fin n)) (edges : List (Fin n × Fin n))
    (hw4 : 4 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (htot_w : 2 * (2 + 2 * edges.length) + n < 2 ^ w) {s : State}
    (hin : s.arrs 0 = [n, edges.length] ++ flatEdges edges)
    (hZ_bit : IsBitSet Z 14 s)
    (hconst : ConstRegs n 4 2 s) :
    ∃ s' t,
      Exec w alg83WriteOutProg s s' t ∧
      t ≤ 17 * n + 34 * edges.length + 100 ∧
      s'.arrs outArr = bitSetList Z ++ ([n, edges.length] ++ flatEdges edges) ∧
      s'.arrs 0 = [n, edges.length] ++ flatEdges edges ∧
      IsBitSet Z 14 s' ∧
      ConstRegs n 4 2 s' ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  have h2m_w : 2 * edges.length < 2 ^ w := by omega
  let len₁ := 2 + 2 * edges.length
  have hlen₁_w : len₁ < 2 ^ w := by dsimp [len₁]; omega
  have h2len₁_w : 2 * len₁ < 2 ^ w := by dsimp [len₁]; omega
  have hn_len₁_w : n + len₁ < 2 ^ w := by dsimp [len₁]; omega
  have h1_idx : 1 < (s.arrs 0).length := by simp [hin, length_flatEdges]
  have h1_val : (s.arrs 0)[1]'h1_idx = edges.length := by simp [hin]
  let s₁ := s.setReg 1 edges.length
  have hex₁ : Exec w (.assign 1 (.read 0 (.const 1))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hw, h1_idx, h1_val, hm_w])
  let s₂ := s₁.setReg 20 len₁
  have hex₂ : Exec w (.assign 20 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))) s₁ s₂ 6 :=
    .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hm_w, h2m_w, len₁, hlen₁_w])
  let s₃ := s₂.setReg 21 (n + len₁)
  have hex₃ : Exec w (.assign 21 (.op .add (.reg 14) (.reg 20))) s₂ s₃ 4 :=
    .assign (by simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hconst.1, hn_w, hlen₁_w, hn_len₁_w])
  let s₄ := s₃.setArr outArr (List.replicate (n + len₁) 0)
  have hex₄ : Exec w (.alloc outArr (.reg 21)) s₃ s₄ (1 + (n + len₁)) :=
    .alloc (by simp [s₃, Expr.eval, checkWord, hn_len₁_w])
  have hconst₄ : ConstRegs n 4 2 s₄ :=
    hconst.of_regs_eq (by simp [s₄, s₃, s₂, s₁, State.setReg])
      (by simp [s₄, s₃, s₂, s₁, State.setReg]) (by simp [s₄, s₃, s₂, s₁, State.setReg])
  have hZ_arr₄ : s₄.arrs 14 = bitSetList Z := by
    simp [s₄, s₃, s₂, s₁, hZ_bit.arr_eq_bitSetList]
  have hout₄ : s₄.arrs outArr = [] ++ List.replicate n 0 ++ List.replicate len₁ 0 := by
    simp only [s₄, State.setArr_arrs_self, List.nil_append]
    exact List.replicate_add n len₁ 0
  have hZ_w : ∀ v ∈ bitSetList Z, v < 2 ^ w := by
    intro v hv
    rcases List.mem_iff_getElem.mp hv with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one Z idx hidx
    omega
  rcases copyToOutProg_exec (w := w) (n := n) (off := 0) 14 (.const 0) 2 (by decide)
      [] (bitSetList Z) (List.replicate len₁ 0)
      rfl (length_bitSetList Z) hZ_w hw (by omega) hconst₄
      (by simp [Expr.eval, checkWord, h0_w]) hZ_arr₄ hout₄ with
    ⟨s₅, t₅, hex₅, ht₅, _, hout₅, harr₅, hreg₅⟩
  dsimp [Expr.cost] at ht₅
  have hr14_₅ : s₅.regs 14 = n := by
    rw [hreg₅ 14 (by decide)]; exact hconst₄.1
  have hr20_₅ : s₅.regs 20 = len₁ := by
    rw [hreg₅ 20 (by decide)]; simp [s₄, s₃, s₂]
  let s₆ := s₅.setReg 22 n
  have hex₆ : Exec w (.assign 22 (.reg 14)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr14_₅, hn_w])
  let s₇ := s₆.setReg 14 len₁
  have hex₇ : Exec w (.assign 14 (.reg 20)) s₆ s₇ 2 :=
    .assign (by simp [s₆, State.setReg, Expr.eval, checkWord, hr20_₅, hlen₁_w])
  let s₈ := s₇.setReg 15 (2 * len₁)
  have hex₈ : Exec w (.assign 15 (.op .mul (.const 2) (.reg 14))) s₇ s₈ 4 :=
    .assign (by simp [s₇, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hlen₁_w, h2len₁_w])
  let s₉ := s₈.setReg 16 0
  have hex₉ : Exec w (.assign 16 (.const 0)) s₈ s₉ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hconst₉ : ConstRegs len₁ 0 2 s₉ :=
    ⟨by simp [s₉, s₈, s₇, State.setReg],
     by simp [s₉, s₈, State.setReg],
     by simp [s₉]⟩
  have henc_w : ∀ v ∈ [n, edges.length] ++ flatEdges edges, v < 2 ^ w := by
    intro v hv
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl) | hv_flat
    · exact hn_w
    · exact hm_w
    · exact Nat.lt_trans (mem_flatEdges_lt edges v hv_flat) hn_w
  have hin₉ : s₉.arrs 0 = [n, edges.length] ++ flatEdges edges := by
    change s₅.arrs 0 = _
    rw [harr₅ 0 (by decide)]
    simp [s₄, s₃, s₂, s₁, hin]
  have hout₉ : s₉.arrs outArr = bitSetList Z ++ List.replicate len₁ 0 ++ [] := by
    simpa [s₉, s₈, s₇, s₆] using hout₅
  rcases copyToOutProg_exec (w := w) (n := len₁) (off := n) 0 (.reg 22) 2 (by decide)
      (bitSetList Z) ([n, edges.length] ++ flatEdges edges) []
      (length_bitSetList Z) (by simp [len₁, length_flatEdges]; omega) henc_w hw hn_len₁_w hconst₉
      (by simp [s₉, s₈, s₇, s₆, State.setReg, Expr.eval, checkWord, hn_w]) hin₉ hout₉ with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, _, hout₁₀, harr₁₀, hreg₁₀⟩
  dsimp [Expr.cost] at ht₁₀
  rw [List.append_nil] at hout₁₀
  have hr22_₁₀ : s₁₀.regs 22 = n := by
    rw [hreg₁₀ 22 (by decide)]
    simp [s₉, s₈, s₇, s₆, State.setReg]
  let s₁₁ := s₁₀.setReg 14 n
  have hex₁₁ : Exec w (.assign 14 (.reg 22)) s₁₀ s₁₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr22_₁₀, hn_w])
  let s₁₂ := s₁₁.setReg 15 (2 * n)
  have hex₁₂ : Exec w (.assign 15 (.op .mul (.const 2) (.reg 14))) s₁₁ s₁₂ 4 :=
    .assign (by simp [s₁₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hn_w, h2n_w])
  let s₁₃ := s₁₂.setReg 16 4
  have hex₁₃ : Exec w (.assign 16 (.const 4)) s₁₂ s₁₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw4])
  have harr_ne : ∀ a : Arr, a ≠ outArr → s₁₃.arrs a = s.arrs a := by
    intro a ha
    change s₁₀.arrs a = s.arrs a
    rw [harr₁₀ a ha]
    change s₅.arrs a = s.arrs a
    rw [harr₅ a ha]
    simp [s₄, s₃, s₂, s₁, ha]
  refine ⟨s₁₃,
    3 + (6 + (4 + ((1 + (n + len₁)) + (t₅ + (2 + (2 + (4 + (2 + (t₁₀ + (2 + (4 + 2))))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
      (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ hex₁₃))))))))))),
    by dsimp [len₁]; omega,
    hout₁₀,
    by rw [harr_ne 0 (by decide), hin],
    hZ_bit.of_arr_eq (harr_ne 14 (by decide)),
    ⟨by simp [s₁₃, s₁₂, s₁₁, State.setReg],
     by simp [s₁₃, s₁₂, State.setReg],
     by simp [s₁₃]⟩,
    harr_ne⟩

/-- Complete Word RAM program for GM XIII Algorithm (8.3):
1. Initializes `ConstRegs x.n 4 2`, `IsBitSet x.omega.toFinset 9`, `IsBitSet Finset.univ 14`,
   and truncates `inArr = 0` to `[x.n, m₀] ++ flatEdges (edgeListOf x.G)` (`initAlg83Prog`).
2. Runs the vertex loop over `v = 0 .. x.n - 1` (`alg83LoopProg`).
3. Serializes `bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C)` to `outArr = 1`
   (`alg83WriteOutProg`). -/
def alg83Prog : Cmd :=
  .seq initAlg83Prog
    (.seq alg83LoopProg
      alg83WriteOutProg)

theorem alg83Prog_exec {w : ℕ} (x : Alg81Input)
    (hw4 : 4 < 2 ^ w)
    (hsize_w : 16 * (alg81Size x + 2) < 2 ^ w) {s₀ : State}
    (hs₀ : s₀.arrs 0 = encAlg81In x) :
    ∃ s' t Z C edges_C,
      Exec w alg83Prog s₀ s' t ∧
      t ≤ 3600 * alg81Size x ∧
      Alg83Trace x Z C ∧
      x.omega.toFinset ⊆ Z ∧
      (∀ u u' : Fin x.n, C.Adj u u' → u ∈ Z ∧ u' ∈ Z) ∧
      IsFourLinkedCore x.omega Z C ∧
      IsSimpleEdgeList C edges_C ∧
      edges_C.length ≤ (edgeListOf x.G).length + 3 * x.n ∧
      s'.arrs outArr = bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C) ∧
      s'.arrs 0 = [x.n, edges_C.length] ++ flatEdges edges_C ∧
      IsBitSet Z 14 s' ∧
      IsBitSet x.omega.toFinset 9 s' ∧
      ConstRegs x.n 4 2 s' := by
  let edges₀ := edgeListOf x.G
  have hm_eq : edges₀.length = x.G.edgeFinset.card :=
    length_edgeListOf_eq_card_edgeFinset x.G
  have hk_le_n : x.omega.length ≤ x.n := length_omega_le_n x.nodup_omega
  have hS_def : alg81Size x = (x.n + 1) * (edges₀.length + x.n + 1) := by
    dsimp [alg81Size, societySize]; rw [hm_eq]
  have hS_ge : edges₀.length + x.n + 1 ≤ alg81Size x := by
    rw [hS_def]
    have : 1 * (edges₀.length + x.n + 1) ≤ (x.n + 1) * (edges₀.length + x.n + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h2n_w : 2 * x.n < 2 ^ w := by omega
  have hin_w : 3 + 2 * edges₀.length + x.omega.length < 2 ^ w := by omega
  have hm_max_w : 8 + 2 * (edges₀.length + 3 * x.n) < 2 ^ w := by omega
  -- 1. initAlg83Prog
  rcases initAlg83Prog_exec x hw4 h2n_w hin_w hs₀ with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, hom₁, hZ₁, hconst₁, _, _⟩
  -- 2. alg83LoopProg
  rcases alg83LoopProg_exec x hw4 h2n_w hm_max_w hin₁ hom₁ hZ₁ hconst₁ with
    ⟨s₂, t₂, hex₂, ht₂, hinv₂, _⟩
  rcases hinv₂ with ⟨Z, C, edges_C, htrace, hom_sub, hadj_Z, hprev,
    hedges_C, hlen_C, hin₂, hZ₂, hom₂, hconst₂, _⟩
  have htot_w : 2 * (2 + 2 * edges_C.length) + x.n < 2 ^ w := by
    have hlen_C' : edges_C.length ≤ edges₀.length + 3 * x.n := hlen_C
    linarith [hsize_w, hS_ge, hlen_C']
  -- 3. alg83WriteOutProg
  rcases alg83WriteOutProg_exec Z edges_C hw4 h2n_w htot_w hin₂ hZ₂ hconst₂ with
    ⟨s₃, t₃, hex₃, ht₃, hout₃, hin₃, hZ₃, hconst₃, harr₃⟩
  have hom₃ : IsBitSet x.omega.toFinset 9 s₃ :=
    hom₂.of_arr_eq (harr₃ 9 (by decide))
  have hcore4 : IsFourLinkedCore x.omega Z C :=
    ⟨hom_sub, hadj_Z, fun u huZ => hprev u huZ u.2⟩
  have htime : t₁ + (t₂ + t₃) ≤ 3600 * alg81Size x := by
    have hstep_le : 2850 * x.n + 520 * edges₀.length + 737 ≤
        2850 * (edges₀.length + x.n + 1) := by
      linarith
    have hloop_le : x.n * (2850 * x.n + 520 * edges₀.length + 737) ≤
        x.n * (2850 * (edges₀.length + x.n + 1)) :=
      Nat.mul_le_mul_left x.n hstep_le
    have hmul_expand : (x.n + 1) * (edges₀.length + x.n + 1) =
        x.n * (edges₀.length + x.n + 1) + (edges₀.length + x.n + 1) :=
      Nat.succ_mul x.n _
    have hS_3600 : 3600 * alg81Size x =
        3600 * (x.n * (edges₀.length + x.n + 1)) + 3600 * (edges₀.length + x.n + 1) := by
      rw [hS_def, hmul_expand, Nat.mul_add]
    have ht₁' : t₁ ≤ 13 * x.n + 64 * edges₀.length + 15 * x.omega.length + 130 := ht₁
    have ht₂' : t₂ ≤ x.n * (2850 * x.n + 520 * edges₀.length + 737) + 5 := ht₂
    have hlen_C' : edges_C.length ≤ edges₀.length + 3 * x.n := hlen_C
    linarith [ht₁', ht₂', ht₃, hlen_C', hk_le_n, hloop_le, hS_3600]
  exact ⟨s₃, t₁ + (t₂ + t₃), Z, C, edges_C,
    .seq hex₁ (.seq hex₂ hex₃), htime,
    htrace, hom_sub, hadj_Z, hcore4, hedges_C, hlen_C,
    hout₃, hin₃, hZ₃, hom₃, hconst₃⟩

/-- **Graph Minors XIII, (8.3) Algorithm** (pages 93–94):
Given a society `(G, Ω)`, `alg83Prog` computes in time `O(vε)` (`alg81Size x`) a 4-linked core
`(Z, C)` together with a valid sequence of (8.2) core steps (`Alg83Trace x Z C`) and four
`({v}, Ω)`-paths witnessing 4-linkedness for every vertex `v ∈ Z`. -/
theorem gm13_algorithm_8_3 :
    ComputesArrRelInTime alg81Size encAlg81In
      (fun x out => IsValidAlg83Output x (decAlg83Out x out))
      alg83Prog (fun s => s) := by
  unfold ComputesArrRelInTime ComputesRelInTime
  refine ⟨3600, 4, by omega, by omega, fun x s₀ hs₀ => ?_⟩
  let w := wordSize 4 (alg81Size x)
  have hpow4 : (alg81Size x + 2) ^ 4 < 2 ^ w :=
    pow_lt_two_pow_wordSize (c := 4) (by omega) (alg81Size x)
  have h16_le : 16 * (alg81Size x + 2) ≤ (alg81Size x + 2) ^ 4 := by
    have h2 : 2 ≤ alg81Size x + 2 := by omega
    have h16 : 16 ≤ (alg81Size x + 2) ^ 3 := by
      have hS_pos : 1 ≤ alg81Size x := by
        dsimp [alg81Size, societySize]; exact Nat.mul_pos (by omega) (by omega)
      have h3 : 3 ≤ alg81Size x + 2 := by omega
      calc 16 ≤ 3 ^ 3 := by decide
        _ ≤ (alg81Size x + 2) ^ 3 := Nat.pow_le_pow_left h3 3
    have hmul := Nat.mul_le_mul_right (alg81Size x + 2) h16
    simpa [Nat.pow_succ] using hmul
  have hsize_w : 16 * (alg81Size x + 2) < 2 ^ w := Nat.lt_of_le_of_lt h16_le hpow4
  have hw4 : 4 < 2 ^ w := by omega
  rcases alg83Prog_exec x hw4 hsize_w hs₀ with
    ⟨s', t, Z, C, edges_C, hex, ht, htrace, hom_sub, hadj_Z, hcore4, hedges_C, _, hout, _, _, _, _⟩
  refine ⟨s', t, hex, ht, ?_⟩
  dsimp only
  rw [hout, decAlg83Out_eq x Z C edges_C hedges_C]
  refine ⟨htrace.isCoreOf, isFourLinkedCore_toCoreGraph htrace hcore4,
    htrace, hom_sub, hadj_Z, hcore4, fun v hvZ => ?_⟩
  exact fourLinkedPaths_of_isFourLinkedAt x.omega Z C v hom_sub hadj_Z hvZ (hcore4.2.2 v hvZ)

end GraphMinor.Compute
