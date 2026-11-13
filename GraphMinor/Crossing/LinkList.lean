module

public import GraphMinor.Crossing.Defs
public import GraphMinor.Crossing.PlanarLemma4
import GraphMinor.HP25.CrossTools

/-!
# Crossings as vertex lists and Lemma 4 for lists (Sections 3 and 5.3 of the note)

The Word RAM programs of the crossing extractor (`docs/crossing/crossing_extractor.tex`) store
paths and crossings as vertex lists (`IsPathList`, `IsDPathList`, `IsCrossingPair`,
`InDistinctBridges` in `GraphMinor/Crossing/Defs.lean`), whereas Humeau and Pous
(`GraphMinor/HP25/Defs.lean`) and `lemma_4` (`GraphMinor/Crossing/PlanarLemma4.lean`) use walks
(`HP25.IsTPath`, `HP25.IsCrossing`, `HP25.IsCrossed`).

This file proves the first two links of the crossing extractor:
* **Crossings as lists**:
  * `exists_isCrossing_of_isCrossingPair`: from `IsCrossingPair G D L₁ L₂`, constructs walks `Q`
    and `R` with `HP25.IsCrossing G D Q R` whose supports are `L₁` and `L₂`, each possibly reversed
    and in either order.
  * `isCrossed_iff_exists_isCrossingPair`: for a cycle `D` (or any duplicate-free list `D`),
    `HP25.IsCrossed G D ↔ ∃ L₁ L₂, IsCrossingPair G D L₁ L₂`.
* **Lemma 4 for lists** (`inDistinctBridges_of_planar` / `lemma_4_list`):
  "Every crossing in a planar graph uses distinct cycle bridges." If `G` is planar on
  `S`, supported on `S`, `D` is a cycle of `G`, and `IsCrossingPair G D L₁ L₂`, then
  `InDistinctBridges G D L₁ L₂`.
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {S : Set V} {D : List V}

/-! ### Path lists, inner vertices, and walks -/

/-- A vertex in `inner L` belongs to `L.tail`. -/
theorem mem_tail_of_mem_inner {L : List V} {x : V} (hx : x ∈ inner L) : x ∈ L.tail :=
  List.dropLast_subset _ hx

/-- A vertex in `inner L` belongs to `L`. -/
theorem mem_of_mem_inner {L : List V} {x : V} (hx : x ∈ inner L) : x ∈ L :=
  List.mem_of_mem_tail (mem_tail_of_mem_inner hx)

/-- If `L` has ends `a` and `b` and length at least `2`, any vertex of `L` other than `a` and `b`
lies in `inner L`. -/
theorem mem_inner_of_ne_ends {L : List V} {a b x : V} (hends : HasEnds L a b)
    (hlen : 2 ≤ L.length) (hx : x ∈ L) (hxa : x ≠ a) (hxb : x ≠ b) : x ∈ inner L := by
  obtain ⟨hhead, hlast⟩ := hends
  rcases L with _ | ⟨u, t⟩
  · simp at hhead
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst hhead
  rcases List.mem_cons.mp hx with rfl | hxt
  · exact absurd rfl hxa
  have htne : t ≠ [] := by
    rintro rfl
    simp at hlen
  have htlast : t.getLast htne = b := by
    rw [List.getLast?_cons_of_ne_nil htne, List.getLast?_eq_some_getLast htne,
      Option.some.injEq] at hlast
    exact hlast
  have htsplit : t = t.dropLast ++ [b] := by
    rw [← htlast]
    exact (List.dropLast_append_getLast htne).symm
  rw [htsplit, List.mem_append, List.mem_singleton] at hxt
  rcases hxt with hxd | rfl
  · exact hxd
  · exact absurd rfl hxb

/-- If `L` has no duplicate vertices and has ends `a` and `b`, no vertex in `inner L` equals `a` or
`b`. -/
theorem ne_ends_of_mem_inner {L : List V} {a b x : V} (hnd : L.Nodup) (hends : HasEnds L a b)
    (hx : x ∈ inner L) : x ≠ a ∧ x ≠ b := by
  obtain ⟨hhead, hlast⟩ := hends
  rcases L with _ | ⟨u, t⟩
  · simp [inner] at hx
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst hhead
  obtain ⟨hut, hndt⟩ := List.nodup_cons.mp hnd
  have hxt : x ∈ t := mem_tail_of_mem_inner hx
  have hxa : x ≠ u := fun h => hut (h ▸ hxt)
  have htne : t ≠ [] := List.ne_nil_of_mem hxt
  have htlast : t.getLast htne = b := by
    rw [List.getLast?_cons_of_ne_nil htne, List.getLast?_eq_some_getLast htne,
      Option.some.injEq] at hlast
    exact hlast
  have htsplit : t = t.dropLast ++ [b] := by
    rw [← htlast]
    exact (List.dropLast_append_getLast htne).symm
  rw [htsplit] at hndt
  have hdisj := (List.nodup_append.mp hndt).2.2
  have hxb : x ≠ b := fun h => hdisj x hx b (List.mem_singleton_self b) h
  exact ⟨hxa, hxb⟩

/-- From a chain `L` in `G` with `HasEnds L a b`, construct a walk `p : G.Walk a b` with
`p.support = L`. -/
theorem exists_walk_of_isChain :
    ∀ {L : List V} {a b : V}, L ≠ [] → L.IsChain G.Adj → HasEnds L a b →
      ∃ p : G.Walk a b, p.support = L
  | [], _, _, hne, _, _ => absurd rfl hne
  | [x], a, b, _, _, ⟨hhead, hlast⟩ => by
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
    subst hhead; subst hlast
    exact ⟨Walk.nil, rfl⟩
  | x :: y :: rest, a, b, _, hchain, ⟨hhead, hlast⟩ => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    rw [List.getLast?_cons_cons] at hlast
    obtain ⟨hadj, hchain'⟩ := List.isChain_cons_cons.mp hchain
    obtain ⟨p, hp⟩ := exists_walk_of_isChain (List.cons_ne_nil y rest) hchain' ⟨rfl, hlast⟩
    exact ⟨Walk.cons hadj p, by simp [hp]⟩

/-- From a path list `L` of `G` with `HasEnds L a b`, construct a path `p : G.Walk a b` with
`p.support = L`. -/
theorem exists_path_of_isPathList {L : List V} {a b : V} (hP : IsPathList G L)
    (hends : HasEnds L a b) : ∃ p : G.Walk a b, p.IsPath ∧ p.support = L := by
  obtain ⟨hne, hnd, hchain⟩ := hP
  obtain ⟨p, hp⟩ := exists_walk_of_isChain hne hchain hends
  exact ⟨p, Walk.IsPath.mk' (hp ▸ hnd), hp⟩

/-- From a `D`-path list `L` of `G` with `HasEnds L a b`, construct a `D`-path `p : G.Walk a b` with
`p.support = L`. -/
theorem exists_isTPath_of_isDPathList {L : List V} {a b : V} (hL : IsDPathList G D L)
    (hends : HasEnds L a b) : ∃ p : G.Walk a b, HP25.IsTPath G D p ∧ p.support = L := by
  obtain ⟨hP, hlen, haD, hbD, hinner⟩ := hL
  obtain ⟨p, hpath, hp⟩ := exists_path_of_isPathList hP hends
  refine ⟨p, ⟨hpath, haD a hends.1, hbD b hends.2, fun x hx hxa hxb => ?_⟩, hp⟩
  rw [hp] at hx
  have hx_in : x ∈ inner L := mem_inner_of_ne_ends hends hlen hx hxa hxb
  exact ⟨hinner x hx_in, hinner x hx_in⟩

/-- From a `D`-path list `L` of `G` with `HasEndsUnordered L a b`, construct a `D`-path
`p : G.Walk a b` whose support is `L` or `L.reverse`. -/
theorem exists_isTPath_of_isDPathList_unordered {L : List V} {a b : V} (hL : IsDPathList G D L)
    (hends : HasEndsUnordered L a b) :
    ∃ p : G.Walk a b, HP25.IsTPath G D p ∧ (p.support = L ∨ p.support = L.reverse) := by
  rcases hends with hab | hba
  · obtain ⟨p, hp, hsupp⟩ := exists_isTPath_of_isDPathList hL hab
    exact ⟨p, hp, Or.inl hsupp⟩
  · obtain ⟨p, hp, hsupp⟩ := exists_isTPath_of_isDPathList hL hba
    exact ⟨p.reverse, HP25.IsTPath.reverse hp, Or.inr (by rw [Walk.support_reverse, hsupp])⟩

/-- The support of a `D`-path `p : G.Walk a b` with distinct endpoints `a ≠ b` is a `D`-path list
with ends `a` and `b`. -/
theorem isDPathList_support_of_isTPath {a b : V} {p : G.Walk a b} (hp : HP25.IsTPath G D p)
    (hne : a ≠ b) : IsDPathList G D p.support ∧ HasEnds p.support a b := by
  obtain ⟨hpath, haD, hbD, hin⟩ := hp
  have hhead : p.support.head? = some a := by
    rw [← Walk.cons_tail_support]
    rfl
  have hlast : p.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast (Walk.support_ne_nil p), Walk.getLast_support]
  have hends : HasEnds p.support a b := ⟨hhead, hlast⟩
  have hlen : 2 ≤ p.support.length := by
    rcases p with _ | ⟨_, q⟩
    · exact absurd rfl hne
    · simp only [Walk.support_cons, List.length_cons]
      have : 1 ≤ q.support.length := List.length_pos_iff.mpr (Walk.support_ne_nil q)
      omega
  have hP : IsPathList G p.support :=
    ⟨Walk.support_ne_nil p, hpath.support_nodup, p.isChain_adj_support⟩
  refine ⟨⟨hP, hlen, ?_, ?_, ?_⟩, hends⟩
  · intro u hu
    rw [hhead, Option.some.injEq] at hu
    exact hu ▸ haD
  · intro v hv
    rw [hlast, Option.some.injEq] at hv
    exact hv ▸ hbD
  · intro y hy
    obtain ⟨hya, hyb⟩ := ne_ends_of_mem_inner hpath.support_nodup hends hy
    exact (hin y (mem_of_mem_inner hy) hya hyb).1

/-! ### Link (a): Crossings as lists -/

/-- Symmetry of `IsCrossingPair` in its two path lists. -/
theorem IsCrossingPair.swap {L₁ L₂ : List V} (h : IsCrossingPair G D L₁ L₂) :
    IsCrossingPair G D L₂ L₁ := by
  obtain ⟨h₁, h₂, hdisj, i, r, j, s, hir, hrj, hjs, a, c, b, d, hi, hr, hj, hs, hends⟩ := h
  exact ⟨h₂, h₁, hdisj.symm, i, r, j, s, hir, hrj, hjs, a, c, b, d, hi, hr, hj, hs,
    hends.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)⟩

/-- **Link (a), walk extraction**: from `IsCrossingPair G D L₁ L₂`, there are walks `Q` and `R`
forming a crossing `HP25.IsCrossing G D Q R` whose supports are `L₁` and `L₂`, each possibly
reversed and in either order. -/
theorem exists_isCrossing_of_isCrossingPair {L₁ L₂ : List V} (h : IsCrossingPair G D L₁ L₂) :
    ∃ (a b c d : V) (Q : G.Walk a b) (R : G.Walk c d),
      HP25.IsCrossing G D Q R ∧
      (((Q.support = L₁ ∨ Q.support = L₁.reverse) ∧
          (R.support = L₂ ∨ R.support = L₂.reverse)) ∨
        ((Q.support = L₂ ∨ Q.support = L₂.reverse) ∧
          (R.support = L₁ ∨ R.support = L₁.reverse))) := by
  obtain ⟨h₁, h₂, hdisj, i, r, j, s, hir, hrj, hjs, a, c, b, d, hi, hr, hj, hs, hends⟩ := h
  have hmem_eq : ∀ {M K : List V}, M = K ∨ M = K.reverse → ∀ x, x ∈ M ↔ x ∈ K := by
    intro M K hMK x
    rcases hMK with rfl | rfl
    · exact Iff.rfl
    · exact List.mem_reverse
  rcases hends with ⟨he₁, he₂⟩ | ⟨he₁, he₂⟩
  · obtain ⟨Q, hQ, hQsupp⟩ := exists_isTPath_of_isDPathList_unordered h₁ he₁
    obtain ⟨R, hR, hRsupp⟩ := exists_isTPath_of_isDPathList_unordered h₂ he₂
    have hdisjQR : Q.support.Disjoint R.support := fun x hxQ hxR =>
      hdisj ((hmem_eq hQsupp x).mp hxQ) ((hmem_eq hRsupp x).mp hxR)
    exact ⟨a, b, c, d, Q, R, ⟨⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ, hR, hdisjQR⟩,
      Or.inl ⟨hQsupp, hRsupp⟩⟩
  · obtain ⟨Q, hQ, hQsupp⟩ := exists_isTPath_of_isDPathList_unordered h₂ he₂
    obtain ⟨R, hR, hRsupp⟩ := exists_isTPath_of_isDPathList_unordered h₁ he₁
    have hdisjQR : Q.support.Disjoint R.support := fun x hxQ hxR =>
      hdisj.symm ((hmem_eq hQsupp x).mp hxQ) ((hmem_eq hRsupp x).mp hxR)
    exact ⟨a, b, c, d, Q, R, ⟨⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ, hR, hdisjQR⟩,
      Or.inr ⟨hQsupp, hRsupp⟩⟩

/-- Every crossing pair gives a crossing of `D` in `G`. -/
theorem IsCrossingPair.isCrossed {L₁ L₂ : List V} (h : IsCrossingPair G D L₁ L₂) :
    HP25.IsCrossed G D := by
  obtain ⟨a, b, c, d, Q, R, hcross, -⟩ := exists_isCrossing_of_isCrossingPair h
  exact ⟨a, b, c, d, Q, R, hcross⟩

/-- If `D` has no duplicate vertices, the supports of a crossing `HP25.IsCrossing G D Q R` form a
crossing pair `IsCrossingPair G D Q.support R.support`. -/
theorem isCrossingPair_of_isCrossing {a b c d : V} {Q : G.Walk a b} {R : G.Walk c d}
    (hD : D.Nodup) (h : HP25.IsCrossing G D Q R) :
    IsCrossingPair G D Q.support R.support := by
  obtain ⟨⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ, hR, hdisj⟩ := h
  obtain ⟨hil, hi'⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hrl, hr'⟩ := List.getElem?_eq_some_iff.mp hr
  obtain ⟨hjl, hj'⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hsl, hs'⟩ := List.getElem?_eq_some_iff.mp hs
  have hab : a ≠ b := by
    intro heq
    have := (List.Nodup.getElem_inj_iff hD).mp (hi'.trans (heq.trans hj'.symm))
    omega
  have hcd : c ≠ d := by
    intro heq
    have := (List.Nodup.getElem_inj_iff hD).mp (hr'.trans (heq.trans hs'.symm))
    omega
  obtain ⟨hQD, hQends⟩ := isDPathList_support_of_isTPath hQ hab
  obtain ⟨hRD, hRends⟩ := isDPathList_support_of_isTPath hR hcd
  exact ⟨hQD, hRD, hdisj, i, r, j, s, hir, hrj, hjs, a, c, b, d, hi, hr, hj, hs,
    Or.inl ⟨Or.inl hQends, Or.inl hRends⟩⟩

/-- **Link (a), equivalence (duplicate-free tuple)**: if `D.Nodup`, `D` is crossed in `G` if and
only if there is a crossing pair `IsCrossingPair G D L₁ L₂`. -/
theorem isCrossed_iff_exists_isCrossingPair_of_nodup (hD : D.Nodup) :
    HP25.IsCrossed G D ↔ ∃ L₁ L₂, IsCrossingPair G D L₁ L₂ := by
  constructor
  · rintro ⟨a, b, c, d, Q, R, hcross⟩
    exact ⟨Q.support, R.support, isCrossingPair_of_isCrossing hD hcross⟩
  · rintro ⟨L₁, L₂, hpair⟩
    exact hpair.isCrossed

/-- **Link (a), equivalence**: for a cycle `D` of `G`, `HP25.IsCrossed G D ↔ ∃ L₁ L₂, IsCrossingPair G D L₁ L₂`. -/
theorem isCrossed_iff_exists_isCrossingPair (hD : HP25.IsCycleList G D) :
    HP25.IsCrossed G D ↔ ∃ L₁ L₂, IsCrossingPair G D L₁ L₂ :=
  isCrossed_iff_exists_isCrossingPair_of_nodup hD.2.1

/-! ### Link (b): Lemma 4 for lists -/

/-- Every vertex of a cycle `D` of `G` belongs to `S` when `G` is supported on `S`. -/
theorem mem_of_isCycleList_of_isSupportedOn (hG : HP25.IsSupportedOn G S)
    (hD : HP25.IsCycleList G D) {v : V} (hv : v ∈ D) : v ∈ S := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hlen1 : (D.rotate 1).length = D.length := List.length_rotate D 1
  have hp : (D[i], (D.rotate 1)[i]'(by omega)) ∈ D.zip (D.rotate 1) := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi], by simp⟩
  exact hG (hD.2.2 _ hp)

/-- Every vertex of a walk `p : G.Walk u v` starting at `u ∈ S` belongs to `S` when `G` is supported
on `S`. -/
theorem mem_of_walk_of_isSupportedOn (hG : HP25.IsSupportedOn G S) :
    ∀ {u v : V} (p : G.Walk u v), u ∈ S → ∀ x ∈ p.support, x ∈ S
  | _, _, Walk.nil, hu, x, hx => by
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ hu
  | _, _, Walk.cons hadj q, hu, x, hx => by
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hxq
    · exact hu
    · exact mem_of_walk_of_isSupportedOn hG q (hG hadj.symm) x hxq

/-- **Lemma 4 for lists** (`docs/crossing/crossing_extractor.tex`, Section 5.3):
"Every crossing in a planar graph uses distinct cycle bridges. Therefore
$\operatorname{BridgeCross}$ is complete on planar inputs."

If `G` is planar on `S`, supported on `S`, `D` is a cycle of `G`, and `IsCrossingPair G D L₁ L₂`,
then `InDistinctBridges G D L₁ L₂`. -/
theorem inDistinctBridges_of_planar (hP : Nonempty (HP25.PlaneEmbedding G S))
    (hG : HP25.IsSupportedOn G S) (hD : HP25.IsCycleList G D)
    {L₁ L₂ : List V} (hcross : IsCrossingPair G D L₁ L₂) :
    InDistinctBridges G D L₁ L₂ := by
  obtain ⟨q₁, q₂, r₁, r₂, Q, R, hQR, hsupp⟩ := exists_isCrossing_of_isCrossingPair hcross
  have hDS : ∀ v ∈ D, v ∈ S := fun _ hv => mem_of_isCycleList_of_isSupportedOn hG hD hv
  have hQS : ∀ x ∈ Q.support, x ∈ S :=
    mem_of_walk_of_isSupportedOn hG Q (hDS q₁ hQR.2.1.2.1)
  have hRS : ∀ x ∈ R.support, x ∈ S :=
    mem_of_walk_of_isSupportedOn hG R (hDS r₁ hQR.2.2.1.2.1)
  have hmem_eq : ∀ {M K : List V}, M = K ∨ M = K.reverse → ∀ x, x ∈ M ↔ x ∈ K := by
    intro M K hMK x
    rcases hMK with rfl | rfl
    · exact Iff.rfl
    · exact List.mem_reverse
  intro u₀ hu₀ v₀ hv₀ ⟨W, hWD⟩
  have huL₁ : u₀ ∈ L₁ := mem_of_mem_inner hu₀
  have hvL₂ : v₀ ∈ L₂ := mem_of_mem_inner hv₀
  rcases hsupp with ⟨hQ₁, hR₂⟩ | ⟨hQ₂, hR₁⟩
  · have huQ : u₀ ∈ Q.support := (hmem_eq hQ₁ u₀).mpr huL₁
    have hvR : v₀ ∈ R.support := (hmem_eq hR₂ v₀).mpr hvL₂
    have hWS : ∀ x ∈ W.support, x ∈ S :=
      mem_of_walk_of_isSupportedOn hG W (hQS u₀ huQ)
    exact lemma_4 hP hD hDS hQR hQS hRS huQ hvR W hWS hWD
  · have hvQ : v₀ ∈ Q.support := (hmem_eq hQ₂ v₀).mpr hvL₂
    have huR : u₀ ∈ R.support := (hmem_eq hR₁ u₀).mpr huL₁
    have hWS : ∀ x ∈ W.reverse.support, x ∈ S :=
      mem_of_walk_of_isSupportedOn hG W.reverse (hQS v₀ hvQ)
    have hWD' : ∀ x ∈ W.reverse.support, x ∉ D := fun x hx =>
      hWD x (List.mem_reverse.mp (Walk.support_reverse W ▸ hx))
    exact lemma_4 hP hD hDS hQR hQS hRS hvQ huR W.reverse hWS hWD'

/-- Alias for `inDistinctBridges_of_planar`. -/
theorem lemma_4_list (hP : Nonempty (HP25.PlaneEmbedding G S))
    (hG : HP25.IsSupportedOn G S) (hD : HP25.IsCycleList G D)
    {L₁ L₂ : List V} (hcross : IsCrossingPair G D L₁ L₂) :
    InDistinctBridges G D L₁ L₂ :=
  inDistinctBridges_of_planar hP hG hD hcross

/-- If `G` is planar on `S`, supported on `S`, `D` is a cycle of `G`, and no crossing pair of `D` in
`G` uses distinct `D`-bridges, then `D` is not crossed in `G` (`Classify`, NO case, Section 6). -/
theorem not_isCrossed_of_planar_of_no_distinctBridges (hP : Nonempty (HP25.PlaneEmbedding G S))
    (hG : HP25.IsSupportedOn G S) (hD : HP25.IsCycleList G D)
    (hno : ∀ L₁ L₂, IsCrossingPair G D L₁ L₂ → ¬ InDistinctBridges G D L₁ L₂) :
    ¬ HP25.IsCrossed G D := by
  rw [isCrossed_iff_exists_isCrossingPair hD]
  rintro ⟨L₁, L₂, hcross⟩
  exact hno L₁ L₂ hcross (inDistinctBridges_of_planar hP hG hD hcross)

end GraphMinor.Crossing
