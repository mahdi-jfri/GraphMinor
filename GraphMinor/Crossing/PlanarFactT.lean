module

public import GraphMinor.HP25.Web
import GraphMinor.HP25.Completion
import GraphMinor.HP25.Lemma43
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.WebPath

/-!
# Fact T and subgraph planarity (`docs/crossing/crossing_extractor.tex`, Section 1)

This file proves subgraph monotonicity for `HP25.PlaneEmbedding` and **Fact T** from Section 1 of
`docs/crossing/crossing_extractor.tex`:

* `HP25.PlaneEmbedding.mono`, `planar_of_subgraph`, `planar_mono`: a subgraph of a planar graph is
  planar.
* `fact_T_on` / `fact_T_finite` / `fact_T`: if `G` is supported on a finite vertex set `S`, `D` is
  a cycle of `G` in `S`, `D` is not crossed in `G`, and `G` is not planar on `S`, then there is a
  nonempty vertex set `U ⊆ S \ {v | v ∈ D}` whose exterior neighbourhood in `G` has at most `3`
  vertices.

Following the note's proof, we extend `G` on `S` to a maximally `D`-crossless graph `G'` on `S`
(`HP25.exists_maxCrosslessOn`), which is a web with frame `D` (`HP25.lemma_4_3_on`). If the web has
no clique vertices (`S = R`), its rib embedding restricts to a plane embedding of `G` on `S`; if it
has a clique vertex `x₀ ∈ S \ R`, the clique `U = {y ∈ S \ R | tri y = tri x₀}` filling the
triangle `tri x₀` is a nonempty subset of `S \ D` whose exterior neighbourhood in `G` is contained
in the three vertices of `tri x₀`.
-/

public section

namespace GraphMinor.HP25.PlaneEmbedding

open SimpleGraph Set

variable {V W : Type*} {G H : SimpleGraph V} {S S' : Set V}

/-- A plane embedding of `G` on `S` restricts to a plane embedding of a subgraph `H` on a subset
`S' ⊆ S`, provided every edge of `H` on `S'` is an edge of `G`. -/
@[expose] def mono (φ : PlaneEmbedding G S) (hGH : ∀ u ∈ S', ∀ v ∈ S', H.Adj u v → G.Adj u v)
    (hSS' : S' ⊆ S) : PlaneEmbedding H S' where
  pt := φ.pt
  line := φ.line
  finite := φ.finite.subset hSS'
  injOn := φ.injOn.mono hSS'
  line_comm := φ.line_comm
  isLine := fun u hu v hv huv => φ.isLine u (hSS' hu) v (hSS' hv) (hGH u hu v hv huv)
  inter := fun u hu v hv u' hu' v' hv' h1 h2 hne =>
    φ.inter u (hSS' hu) v (hSS' hv) u' (hSS' hu') v' (hSS' hv')
      (hGH u hu v hv h1) (hGH u' hu' v' hv' h2) hne
  avoid := fun u hu v hv huv w hw =>
    φ.avoid u (hSS' hu) v (hSS' hv) (hGH u hu v hv huv) w (hSS' hw)

/-- A plane embedding of `G` on `S` pulls back along an injection `f : W → V` to a plane embedding
of `H` on `T`, provided `f` maps `T` into `S` and maps edges of `H` on `T` to edges of `G`. -/
@[expose] def comap {H : SimpleGraph W} {T : Set W} (φ : PlaneEmbedding G S) (f : W → V)
    (hfS : ∀ u ∈ T, f u ∈ S) (hfinj : InjOn f T)
    (hGH : ∀ u ∈ T, ∀ v ∈ T, H.Adj u v → G.Adj (f u) (f v)) : PlaneEmbedding H T where
  pt u := φ.pt (f u)
  line u v := φ.line (f u) (f v)
  finite := (φ.finite.subset (image_subset_iff.mpr hfS)).of_finite_image hfinj
  injOn := fun u hu v hv huv => hfinj hu hv (φ.injOn (hfS u hu) (hfS v hv) huv)
  line_comm u v := φ.line_comm (f u) (f v)
  isLine u hu v hv huv := φ.isLine (f u) (hfS u hu) (f v) (hfS v hv) (hGH u hu v hv huv)
  inter u hu v hv u' hu' v' hv' h1 h2 hne := by
    have hne' : s(f u, f v) ≠ s(f u', f v') := by
      intro he
      apply hne
      rcases Sym2.eq_iff.mp he with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Sym2.eq_iff.mpr (Or.inl ⟨hfinj hu hu' h3, hfinj hv hv' h4⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨hfinj hu hv' h3, hfinj hv hu' h4⟩)
    intro z hz
    obtain ⟨w, ⟨hw1, hw2⟩, rfl⟩ := φ.inter (f u) (hfS u hu) (f v) (hfS v hv)
      (f u') (hfS u' hu') (f v') (hfS v' hv') (hGH u hu v hv h1) (hGH u' hu' v' hv' h2) hne' hz
    rcases hw1 with rfl | rfl
    · refine ⟨u, ⟨Or.inl rfl, ?_⟩, rfl⟩
      rcases hw2 with h3 | h3
      · exact Or.inl (hfinj hu hu' h3)
      · exact Or.inr (hfinj hu hv' h3)
    · refine ⟨v, ⟨Or.inr rfl, ?_⟩, rfl⟩
      rcases hw2 with h3 | h3
      · exact Or.inl (hfinj hv hu' h3)
      · exact Or.inr (hfinj hv hv' h3)
  avoid u hu v hv huv w hw hpt := by
    rcases φ.avoid (f u) (hfS u hu) (f v) (hfS v hv) (hGH u hu v hv huv)
      (f w) (hfS w hw) hpt with h | h
    · exact Or.inl (hfinj hw hu h)
    · exact Or.inr (hfinj hw hv h)

end GraphMinor.HP25.PlaneEmbedding

namespace GraphMinor.Crossing

open SimpleGraph Set GraphMinor.HP25

variable {V : Type*} {G H : SimpleGraph V} {S S' : Set V} {D : List V}

/-- **Subgraph planarity**: a subgraph `H ≤ G` of a graph `G` planar on `S` is planar on any subset
`S' ⊆ S`. -/
theorem planar_of_subgraph (hP : Nonempty (PlaneEmbedding G S)) (hle : H ≤ G) (hSS' : S' ⊆ S) :
    Nonempty (PlaneEmbedding H S') :=
  let ⟨φ⟩ := hP
  ⟨φ.mono (fun _ _ _ _ h => hle h) hSS'⟩

/-- **Subgraph planarity** for graphs agreeing on `S' ⊆ S`: if `G` is planar on `S`, `S' ⊆ S`, and
every edge of `H` with both ends in `S'` is an edge of `G`, then `H` is planar on `S'`. -/
theorem planar_mono (hP : Nonempty (PlaneEmbedding G S))
    (hGH : ∀ u ∈ S', ∀ v ∈ S', H.Adj u v → G.Adj u v) (hSS' : S' ⊆ S) :
    Nonempty (PlaneEmbedding H S') :=
  let ⟨φ⟩ := hP
  ⟨φ.mono hGH hSS'⟩

/-! ### Fact T on a finite vertex type -/

/-- The cardinality of `{a, b, c}` is at most `3`. -/
private theorem ncard_insert_three (a b c : V) : ({a, b, c} : Set V).ncard ≤ 3 :=
  (ncard_insert_le a {b, c}).trans (Nat.add_le_add_right
    ((ncard_insert_le b {c}).trans (by simp)) 1)

/-- **Fact T** (`docs/crossing/crossing_extractor.tex`, Section 1), finite-type version:
"Let \(C\) be a cycle of a graph \(K\). If \(C\) is crossless and \(K\) is nonplanar, then
there is a nonempty set \(U\subseteq V(K)\setminus V(C)\) with \(|N_K(U)|\le 3\)." Graphs in the
note are finite and simple.

The proof follows the note: add edges to `K`, one at a time, as long as `C` stays crossless. This
gives a maximally `C`-crossless graph on the same vertex set, which is a web with frame `C`. If no
clique of the web has a vertex, the web is its rib, which is planar, and so is its subgraph `K`.
Otherwise the vertex set of a nonempty clique is the set `U`. -/
theorem fact_T_finite [Finite V] (hs : IsSupportedOn G S) (hD : IsCycleList G D)
    (hDS : ∀ v ∈ D, v ∈ S) (hnc : ¬ IsCrossed G D) (hnp : ¬ Nonempty (PlaneEmbedding G S)) :
    ∃ U ⊆ S \ {v | v ∈ D}, U.Nonempty ∧
      {z | z ∉ U ∧ ∃ y ∈ U, G.Adj y z}.ncard ≤ 3 ∧
      {z ∈ S \ U | ∃ y ∈ U, G.Adj y z}.ncard ≤ 3 := by
  obtain ⟨G', hle, hmax⟩ := exists_maxCrosslessOn hs hnc
  have hweb : IsWebOn G' S D := lemma_4_3_on S.ncard G' S D rfl (hD.mono hle) hDS hmax
  obtain ⟨R, tri, W⟩ := hweb.exists_webData
  obtain ⟨_, hDR, φ, _⟩ := W.rib
  by_cases hSR : (S \ R).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hSR
    let U : Set V := {y ∈ S \ R | tri y = tri x₀}
    have hx₀U : x₀ ∈ U := ⟨hx₀, rfl⟩
    have hUD : U ⊆ S \ {v | v ∈ D} := by
      rintro y ⟨⟨hyS, hyR⟩, -⟩
      exact ⟨hyS, fun hyD => hyR (hDR y hyD)⟩
    obtain ⟨a, b, c, -, htri⟩ := W.tri_spec x₀ hx₀
    have hN : {z | z ∉ U ∧ ∃ y ∈ U, G.Adj y z} ⊆ {a, b, c} := by
      rintro z ⟨hzU, y, ⟨hySR, hyt⟩, hyz⟩
      rcases (W.adj_iff y hySR z).mp (hle hyz) with hz | ⟨hzSR, -, hzt⟩
      · rwa [hyt, htri] at hz
      · exact absurd ⟨hzSR, hzt.trans hyt⟩ hzU
    have hcard : {z | z ∉ U ∧ ∃ y ∈ U, G.Adj y z}.ncard ≤ 3 :=
      (ncard_le_ncard hN (toFinite {a, b, c})).trans (ncard_insert_three a b c)
    have hsub : {z ∈ S \ U | ∃ y ∈ U, G.Adj y z} ⊆ {z | z ∉ U ∧ ∃ y ∈ U, G.Adj y z} :=
      fun z ⟨⟨_, hzU⟩, hy⟩ => ⟨hzU, hy⟩
    refine ⟨U, hUD, ⟨x₀, hx₀U⟩, hcard,
      (ncard_le_ncard hsub (toFinite _)).trans hcard⟩
  · have hSR' : S ⊆ R := fun x hxS => by_contra fun hxR => hSR ⟨x, hxS, hxR⟩
    exact absurd ⟨φ.mono (fun _ _ _ _ h => hle h) hSR'⟩ hnp

/-! ### Fact T on any type with `S.Finite` -/

private theorem map_val_pmap_subtype :
    ∀ (L : List V) (hL : ∀ v ∈ L, v ∈ S), (L.pmap Subtype.mk hL).map Subtype.val = L
  | [], _ => rfl
  | x :: L, hL => by
    simp [map_val_pmap_subtype L (fun v hv => hL v (List.mem_cons_of_mem x hv))]

/-- Lifting a cycle list from `G` on `S` to `G.induce S`. -/
private theorem isCycleList_pmap_subtype (hD : IsCycleList G D) (hDS : ∀ v ∈ D, v ∈ S) :
    IsCycleList (G.induce S) (D.pmap Subtype.mk hDS) := by
  set D' := D.pmap Subtype.mk hDS
  have hmap : D'.map Subtype.val = D := map_val_pmap_subtype D hDS
  have hlen : D'.length = D.length := by simp [D']
  refine ⟨hlen ▸ hD.1, List.Nodup.of_map Subtype.val (hmap ▸ hD.2.1), ?_⟩
  intro p hp
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hp
  simp only [List.length_zip, List.length_rotate, min_self] at hi
  simp only [List.getElem_zip] at he
  have hmem : ((D'.map Subtype.val)[i]'(by simp [hi]),
      ((D'.rotate 1).map Subtype.val)[i]'(by simp [hi])) ∈ D.zip (D.rotate 1) := by
    have hi' : i < (D.zip (D.rotate 1)).length := by simp [← hlen, hi]
    have h := List.getElem_mem hi'
    simpa [← hmap, ← List.map_rotate] using h
  simp only [List.getElem_map] at hmem
  rw [← he]
  exact hD.2.2 _ hmem

/-- If `D` is crossless in `G`, its lift to `G.induce S` is crossless. -/
private theorem not_isCrossed_pmap_subtype (hDS : ∀ v ∈ D, v ∈ S) (hnc : ¬ IsCrossed G D) :
    ¬ IsCrossed (G.induce S) (D.pmap Subtype.mk hDS) := by
  set D' := D.pmap Subtype.mk hDS
  have hmap : D'.map Subtype.val = D := map_val_pmap_subtype D hDS
  have hmem : ∀ x : ↥S, x ∈ D' ↔ x.1 ∈ D := fun x => by
    rw [← hmap, List.mem_map_of_injective Subtype.val_injective]
  rintro ⟨a, b, c, d, Q, R, ⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ, hR, hdisj⟩
  apply hnc
  let f : G.induce S ↪g G := Embedding.induce S
  let Q' : G.Walk a.1 b.1 := Q.map f.toHom
  let R' : G.Walk c.1 d.1 := R.map f.toHom
  have hget : ∀ (k : ℕ) (x : ↥S), D'[k]? = some x → D[k]? = some x.1 := fun k x hk => by
    rw [← hmap, List.getElem?_map, hk, Option.map_some]
  have hTPath : ∀ {u v : ↥S} (P : (G.induce S).Walk u v),
      IsTPath (G.induce S) D' P → IsTPath G D (P.map f.toHom) := by
    intro u v P ⟨hpath, hu, hv, hin⟩
    have hpath' : (P.map f.toHom).IsPath := by
      rw [Walk.isPath_def, Walk.support_map]
      exact hpath.support_nodup.map f.injective
    refine ⟨hpath', (hmem u).mp hu, (hmem v).mp hv, ?_⟩
    intro x hx hxu hxv
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hin y hy (fun h => hxu (congrArg Subtype.val h)) (fun h => hxv (congrArg Subtype.val h))
    exact ⟨(hmem y).not.mp this.1, (hmem y).not.mp this.2⟩
  refine ⟨a.1, b.1, c.1, d.1, Q', R', ⟨i, r, j, s, hir, hrj, hjs,
    hget i a hi, hget r c hr, hget j b hj, hget s d hs⟩, hTPath Q hQ, hTPath R hR, ?_⟩
  intro x hxQ hxR
  change x ∈ (Q.map f.toHom).support at hxQ
  change x ∈ (R.map f.toHom).support at hxR
  rw [Walk.support_map, List.mem_map] at hxQ hxR
  obtain ⟨y, hyQ, rfl⟩ := hxQ
  obtain ⟨z, hzR, he⟩ := hxR
  exact hdisj hyQ (Subtype.ext he ▸ hzR)

/-- **Fact T** (`docs/crossing/crossing_extractor.tex`, Section 1):
"Let \(C\) be a cycle of a graph \(K\). If \(C\) is crossless and \(K\) is nonplanar, then
there is a nonempty set \(U\subseteq V(K)\setminus V(C)\) with \(|N_K(U)|\le 3\)." Graphs in the
note are finite and simple.

Stated for a graph `G` supported on a finite vertex set `S` (`HP25.IsSupportedOn G S`), without
requiring the ambient type `V` to be finite. -/
theorem fact_T_on (hS : S.Finite) (hs : IsSupportedOn G S) (hD : IsCycleList G D)
    (hDS : ∀ v ∈ D, v ∈ S) (hnc : ¬ IsCrossed G D) (hnp : ¬ Nonempty (PlaneEmbedding G S)) :
    ∃ U ⊆ S \ {v | v ∈ D}, U.Nonempty ∧
      {z | z ∉ U ∧ ∃ y ∈ U, G.Adj y z}.ncard ≤ 3 ∧
      {z ∈ S \ U | ∃ y ∈ U, G.Adj y z}.ncard ≤ 3 := by
  classical
  have : Finite ↥S := hS.to_subtype
  set D' := D.pmap Subtype.mk hDS
  have hmap : D'.map Subtype.val = D := map_val_pmap_subtype D hDS
  have hmem : ∀ x : ↥S, x ∈ D' ↔ x.1 ∈ D := fun x => by
    rw [← hmap, List.mem_map_of_injective Subtype.val_injective]
  have hnp' : ¬ Nonempty (PlaneEmbedding (G.induce S) univ) := by
    rintro ⟨φ⟩
    apply hnp
    let f : V → ↥S := fun v =>
      if hv : v ∈ S then ⟨v, hv⟩ else ⟨D.head (by intro h; simp [h, IsCycleList] at hD),
        hDS _ (List.head_mem _)⟩
    have hf : ∀ v ∈ S, (f v).1 = v := fun v hv => by simp [f, hv]
    refine ⟨φ.comap f (fun _ _ => trivial) (fun u hu v hv huv => by
      have := congrArg Subtype.val huv
      rwa [hf u hu, hf v hv] at this) (fun u hu v hv huv => by
      change G.Adj (f u).1 (f v).1
      rwa [hf u hu, hf v hv])⟩
  obtain ⟨U', hU'D, ⟨x₀, hx₀⟩, hcard', -⟩ := fact_T_finite (G := G.induce S) (S := univ) (D := D')
    (fun _ _ _ => trivial) (isCycleList_pmap_subtype hD hDS) (fun _ _ => trivial)
    (not_isCrossed_pmap_subtype hDS hnc) hnp'
  let U : Set V := Subtype.val '' U'
  have hUD : U ⊆ S \ {v | v ∈ D} := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y.2, fun hyD => (hU'D hy).2 ((hmem y).mpr hyD)⟩
  have hN : {z | z ∉ U ∧ ∃ y ∈ U, G.Adj y z} ⊆
      Subtype.val '' {z | z ∉ U' ∧ ∃ y ∈ U', (G.induce S).Adj y z} := by
    rintro z ⟨hzU, y, ⟨y', hy', rfl⟩, hyz⟩
    have hzS : z ∈ S := hs hyz.symm
    refine ⟨⟨z, hzS⟩, ⟨fun hz' => hzU ⟨⟨z, hzS⟩, hz', rfl⟩, y', hy', hyz⟩, rfl⟩
  have hcard : {z | z ∉ U ∧ ∃ y ∈ U, G.Adj y z}.ncard ≤ 3 :=
    (ncard_le_ncard hN (toFinite _)).trans ((ncard_image_le (toFinite _)).trans hcard')
  have hsub : {z ∈ S \ U | ∃ y ∈ U, G.Adj y z} ⊆ {z | z ∉ U ∧ ∃ y ∈ U, G.Adj y z} :=
    fun z ⟨⟨_, hzU⟩, hy⟩ => ⟨hzU, hy⟩
  have hfinN : {z | z ∉ U ∧ ∃ y ∈ U, G.Adj y z}.Finite := (toFinite _).subset hN
  exact ⟨U, hUD, ⟨x₀.1, x₀, hx₀, rfl⟩, hcard, (ncard_le_ncard hsub hfinN).trans hcard⟩

/-- **Fact T** on `Set.univ` for a finite graph `G`: if `D` is a crossless cycle of `G` and `G` is
not planar, there is a nonempty `U ⊆ univ \ {v | v ∈ D}` whose exterior neighbourhood in `G` has
at most `3` vertices. -/
theorem fact_T [Finite V] (hD : IsCycleList G D) (hnc : ¬ IsCrossed G D)
    (hnp : ¬ Nonempty (PlaneEmbedding G univ)) :
    ∃ U ⊆ {v | v ∉ D}, U.Nonempty ∧ {z | z ∉ U ∧ ∃ y ∈ U, G.Adj y z}.ncard ≤ 3 := by
  obtain ⟨U, hUD, hne, hcard, -⟩ :=
    fact_T_finite (G := G) (S := univ) (fun _ _ _ => trivial) hD (fun _ _ => trivial) hnc hnp
  exact ⟨U, fun x hx => (hUD hx).2, hne, hcard⟩

end GraphMinor.Crossing
