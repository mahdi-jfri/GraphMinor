module

public import GraphMinor.Crossing.PlanarFactT
public import GraphMinor.Surface.CrossCut
import GraphMinor.HP25.EdgeFaces
import GraphMinor.HP25.SplitTools
import GraphMinor.Surface.JordanPlane
import GraphMinor.Surface.PlaneSeparation
import GraphMinor.Surface.SurfaceGraph

/-!
# Faces and Euler's inequality for plane embeddings

This file establishes the face-counting infrastructure and Euler's inequality for
`HP25.PlaneEmbedding`:

* `edgesOn G R`: the set of edges of `G` with both endpoints in `R`.
* `acyclic_edgesOn_bound`: if `G` has no cycle on a finite nonempty set `R`, then
  `(edgesOn G R).ncard + 1 ≤ R.ncard`.
* `HP25.PlaneEmbedding.faces_ncard_of_acyclic`: if `G` has no cycle on `R`, every continuous
  nonvanishing function on `φ.U` has a continuous logarithm, so by Eilenberg's criterion `φ.faces`
  has a single face (`φ.faces.ncard = 1`).
* `HP25.PlaneEmbedding.faces_deleteEdge`: deleting an edge `uv` of `G` on `R` merges the faces
  `f₁, f₂` on the two sides of `φ.line u v` into a single face `f₀` while keeping all other faces
  unchanged.
* `HP25.PlaneEmbedding.faces_finite`: `φ.faces` is finite for every plane embedding `φ`.
* `HP25.PlaneEmbedding.euler_ineq`: for every plane embedding `φ : PlaneEmbedding G R` on a
  nonempty vertex set `R`, `(edgesOn G R).ncard + 2 ≤ R.ncard + φ.faces.ncard`.
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set GraphMinor.HP25 GraphMinor.Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-! ### Edges of a graph on a vertex set -/

/-- The set of edges of `G` with both endpoints in `R`. -/
@[expose] def edgesOn (G : SimpleGraph V) (R : Set V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | ∀ v ∈ e, v ∈ R}

theorem mem_edgesOn_iff {u v : V} :
    s(u, v) ∈ edgesOn G R ↔ u ∈ R ∧ v ∈ R ∧ G.Adj u v := by
  constructor
  · rintro ⟨h, h2⟩
    exact ⟨h2 u (Sym2.mem_mk_left u v), h2 v (Sym2.mem_mk_right u v), h⟩
  · rintro ⟨hu, hv, h⟩
    refine ⟨h, fun x hx => ?_⟩
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact hu
    · exact hv

theorem finite_edgesOn (hR : R.Finite) : (edgesOn G R).Finite := by
  have hsub : edgesOn G R ⊆ (fun p : V × V => s(p.1, p.2)) '' (R ×ˢ R) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgesOn_iff] at he
      exact ⟨(u, v), ⟨he.1, he.2.1⟩, rfl⟩
  exact ((hR.prod hR).image _).subset hsub

theorem edgesOn_empty : edgesOn G (∅ : Set V) = ∅ := by
  ext e
  induction e using Sym2.ind with
  | _ u v => simp [mem_edgesOn_iff]

theorem edgesOn_singleton (u : V) : edgesOn G ({u} : Set V) = ∅ := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_edgesOn_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
    intro ha hb hab
    rw [ha, hb] at hab
    exact G.loopless.irrefl u hab

theorem edgesOn_diff_singleton_eq_of_isolated {u : V} (hu : u ∈ R)
    (hiso : ∀ v ∈ R, ¬ G.Adj u v) :
    edgesOn G R = edgesOn G (R \ {u}) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_edgesOn_iff, mem_sdiff, mem_singleton_iff]
    refine ⟨fun ⟨ha, hb, hab⟩ => ⟨⟨ha, ?_⟩, ⟨hb, ?_⟩, hab⟩,
      fun ⟨⟨ha, _⟩, ⟨hb, _⟩, hab⟩ => ⟨ha, hb, hab⟩⟩
    · rintro rfl; exact hiso b hb hab
    · rintro rfl; exact hiso a ha hab.symm

theorem edgesOn_diff_singleton_insert_of_leaf {u v : V} (hu : u ∈ R) (hv : v ∈ R)
    (huv : G.Adj u v) (hleaf : ∀ w ∈ R, G.Adj u w → w = v) :
    edgesOn G R = insert s(u, v) (edgesOn G (R \ {u})) ∧
      s(u, v) ∉ edgesOn G (R \ {u}) := by
  refine ⟨?_, ?_⟩
  · ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_insert_iff, mem_edgesOn_iff, mem_sdiff, mem_singleton_iff, Sym2.eq_iff]
      constructor
      · rintro ⟨ha, hb, hab⟩
        by_cases hau : a = u
        · subst hau
          exact Or.inl (Or.inl ⟨rfl, hleaf b hb hab⟩)
        · by_cases hbu : b = u
          · subst hbu
            exact Or.inl (Or.inr ⟨hleaf a ha hab.symm, rfl⟩)
          · exact Or.inr ⟨⟨ha, hau⟩, ⟨hb, hbu⟩, hab⟩
      · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨⟨ha, _⟩, ⟨hb, _⟩, hab⟩)
        · exact ⟨hu, hv, huv⟩
        · exact ⟨hv, hu, huv.symm⟩
        · exact ⟨ha, hb, hab⟩
  · simp [mem_edgesOn_iff]

theorem edgesOn_deleteEdges_singleton {u v : V} (hu : u ∈ R) (hv : v ∈ R) (huv : G.Adj u v) :
    edgesOn G R = insert s(u, v) (edgesOn (G.deleteEdges {s(u, v)}) R) ∧
      s(u, v) ∉ edgesOn (G.deleteEdges {s(u, v)}) R := by
  refine ⟨?_, ?_⟩
  · ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_insert_iff, mem_edgesOn_iff, deleteEdges_adj, mem_singleton_iff]
      constructor
      · rintro ⟨ha, hb, hab⟩
        by_cases he : s(a, b) = s(u, v)
        · exact Or.inl he
        · exact Or.inr ⟨ha, hb, hab, he⟩
      · rintro (he | ⟨ha, hb, hab, -⟩)
        · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hu, hv, huv⟩
          · exact ⟨hv, hu, huv.symm⟩
        · exact ⟨ha, hb, hab⟩
  · simp [mem_edgesOn_iff]

/-! ### Cycle-free graphs on a vertex set -/

/-- A path list on a finite set `R` has length at most `R.ncard`. -/
private theorem isPathList_length_le_ncard (hR : R.Finite) {l : List V} (hl : IsPathList G R l) :
    l.length ≤ R.ncard := by
  have h1 : {x | x ∈ l}.ncard ≤ R.ncard := ncard_le_ncard (fun x hx => hl.2.2 x hx) hR
  have h2 : ∀ (L : List V), L.Nodup → (∀ x ∈ L, x ∈ R) → {x | x ∈ L}.ncard = L.length := by
    intro L hnd hLR
    induction L with
    | nil => simp
    | cons a L ih =>
      simp only [List.nodup_cons] at hnd
      have hset : {x | x ∈ a :: L} = insert a {x | x ∈ L} := by
        ext x; simp
      have haL : a ∉ {x | x ∈ L} := hnd.1
      have hfinL : {x | x ∈ L}.Finite := hR.subset (fun x hx => hLR x (List.mem_cons_of_mem a hx))
      rw [hset, ncard_insert_of_notMem haL hfinL,
        ih hnd.2 (fun x hx => hLR x (List.mem_cons_of_mem a hx)), List.length_cons]
  rwa [h2 l hl.1 hl.2.2] at h1

/-- Extending a path list until its start has no neighbours in `R` outside the list. -/
private theorem exists_maximal_pathList (hR : R.Finite) :
    ∀ (k : ℕ) {u : V} {rest : List V}, IsPathList G R (u :: rest) →
      R.ncard - (u :: rest).length ≤ k →
      ∃ (u' : V) (rest' : List V), IsPathList G R (u' :: rest') ∧
        ∀ v ∈ R, G.Adj v u' → v ∈ u' :: rest'
  | 0, u, rest, hP, hk => by
    refine ⟨u, rest, hP, fun v hv hvu => by_contra fun hnot => ?_⟩
    have hP' : IsPathList G R (v :: u :: rest) :=
      ⟨List.nodup_cons.mpr ⟨hnot, hP.1⟩, List.isChain_cons_cons.mpr ⟨hvu, hP.2.1⟩,
        fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hv) (fun hx' => hP.2.2 x hx')⟩
    have hle := isPathList_length_le_ncard hR hP'
    simp only [List.length_cons] at hle hk
    omega
  | k + 1, u, rest, hP, hk => by
    by_cases hext : ∃ v ∈ R, G.Adj v u ∧ v ∉ u :: rest
    · obtain ⟨v, hv, hvu, hnot⟩ := hext
      have hP' : IsPathList G R (v :: u :: rest) :=
        ⟨List.nodup_cons.mpr ⟨hnot, hP.1⟩, List.isChain_cons_cons.mpr ⟨hvu, hP.2.1⟩,
          fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hv) (fun hx' => hP.2.2 x hx')⟩
      have hle := isPathList_length_le_ncard hR hP'
      exact exists_maximal_pathList hR k hP' (by simp only [List.length_cons] at hle hk ⊢; omega)
    · push Not at hext
      exact ⟨u, rest, hP, hext⟩

/-- If `G` has no cycle on a finite nonempty set `R`, then some vertex `u ∈ R` has at most one
neighbour in `R`. -/
theorem exists_deg_le_one_of_acyclic (hR : R.Finite) (hne : R.Nonempty)
    (hacyc : ¬ ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R) :
    ∃ u ∈ R, ∀ v ∈ R, ∀ w ∈ R, G.Adj u v → G.Adj u w → v = w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀⟩ := hne
  have hP₀ : IsPathList G R [x₀] := ⟨by simp, by simp, by simp [hx₀]⟩
  obtain ⟨u, rest, hP, hmax⟩ := exists_maximal_pathList hR (R.ncard - 1) hP₀ le_rfl
  have hu : u ∈ R := hP.2.2 u (by simp)
  obtain ⟨v, hvR, w, hwR, huv, huw, hvw⟩ := hcon u hu
  have hv_mem : v ∈ rest :=
    (List.mem_cons.mp (hmax v hvR huv.symm)).resolve_left huv.ne.symm
  have hw_mem : w ∈ rest :=
    (List.mem_cons.mp (hmax w hwR huw.symm)).resolve_left huw.ne.symm
  rcases rest with _ | ⟨a, t⟩
  · simp at hv_mem
  have hzt : ∃ z ∈ t, G.Adj z u := by
    rcases List.mem_cons.mp hv_mem with rfl | hvt
    · rcases List.mem_cons.mp hw_mem with rfl | hwt
      · exact absurd rfl hvw
      · exact ⟨w, hwt, huw.symm⟩
    · exact ⟨v, hvt, huv.symm⟩
  obtain ⟨z, hzt, hzu⟩ := hzt
  obtain ⟨mid, tail, rfl⟩ := List.append_of_mem hzt
  let C : List V := u :: a :: mid ++ [z]
  have heq : u :: a :: (mid ++ z :: tail) = C ++ tail := by simp [C]
  apply hacyc
  refine ⟨C, ⟨by simp [C], ?_, ?_⟩, ?_⟩
  · have hnd := hP.1
    rw [heq] at hnd
    exact hnd.of_append_left
  · have hch := hP.2.1
    rw [heq] at hch
    have hchC : C.IsChain G.Adj := hch.left_of_append
    have hchCu : (C ++ [u]).IsChain G.Adj := by
      refine hchC.append (by simp) fun x hx y hy => ?_
      have hy' : y = u := Option.some.inj hy.symm
      have hlast : C.getLast? = some z := by
        dsimp [C]
        rw [List.getLast?_eq_some_getLast (by simp)]
        simp
      have hx' : x = z := Option.some.inj (hx.symm.trans hlast)
      exact hx' ▸ hy' ▸ hzu
    have hzip : C.zip (C.rotate 1) = (C ++ [u]).zip (C ++ [u]).tail :=
      zip_rotate_one_cons u (a :: mid ++ [z])
    rw [hzip]
    exact isChain_iff_zip.mp hchCu
  · intro x hx
    exact hP.2.2 x (heq ▸ List.mem_append_left _ hx)

/-- A cycle-free graph on a finite nonempty set `R` has at most `R.ncard - 1` edges on `R`. -/
theorem acyclic_edgesOn_bound :
    ∀ (n : ℕ) {R : Set V}, R.Finite → R.ncard = n → R.Nonempty →
      (¬ ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R) →
      (edgesOn G R).ncard + 1 ≤ R.ncard := by
  intro n
  induction n with
  | zero =>
    intro R hR hn hne _
    exact absurd ((ncard_eq_zero (s := R) hR).mp hn) hne.ne_empty
  | succ n ih =>
    intro R hR hn hne hacyc
    obtain ⟨u, hu, hdeg⟩ := exists_deg_le_one_of_acyclic hR hne hacyc
    have hR' : (R \ {u}).Finite := hR.sdiff
    have hn' : (R \ {u}).ncard = n := by
      have := ncard_sdiff_singleton_add_one hu hR
      omega
    by_cases hne' : (R \ {u}).Nonempty
    · have hacyc' : ¬ ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R \ {u} :=
        fun ⟨C, hC, hCR'⟩ => hacyc ⟨C, hC, fun x hx => (hCR' x hx).1⟩
      have hih := ih hR' hn' hne' hacyc'
      by_cases hadj : ∃ v ∈ R, G.Adj u v
      · obtain ⟨v, hv, huv⟩ := hadj
        obtain ⟨heq, hnot⟩ := edgesOn_diff_singleton_insert_of_leaf hu hv huv
          (fun w hw huw => hdeg w hw v hv huw huv)
        rw [heq, ncard_insert_of_notMem hnot (finite_edgesOn hR')]
        omega
      · push Not at hadj
        rw [edgesOn_diff_singleton_eq_of_isolated hu hadj]
        omega
    · rw [not_nonempty_iff_eq_empty] at hne'
      have hRu : R = {u} := Subset.antisymm
        (fun x hx => by_contra fun hxu => (eq_empty_iff_forall_notMem.mp hne') x ⟨hx, hxu⟩)
        (singleton_subset_iff.mpr hu)
      rw [hRu, edgesOn_singleton, ncard_empty, ncard_singleton]

end GraphMinor.Crossing

/-! ### Logarithms and faces of cycle-free plane embeddings -/

namespace GraphMinor.HP25.PlaneEmbedding

open SimpleGraph Set GraphMinor.Surface GraphMinor.Crossing

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-- Two closed sets meeting in at most one point paste continuous logarithms. -/
private theorem hasLogOn_union_of_subsingleton {T : Type*} [TopologicalSpace T] {A B : Set T}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : (A ∩ B).Subsingleton) {f : T → ℂ}
    (hlogA : HasLogOn A f) (hlogB : HasLogOn B f) : HasLogOn (A ∪ B) f := by
  obtain ⟨gA, hgA, hfA⟩ := hlogA
  obtain ⟨gB, hgB, hfB⟩ := hlogB
  by_cases hne : (A ∩ B).Nonempty
  · obtain ⟨p, hp⟩ := hne
    let c : ℂ := gA p - gB p
    have hexpc : Complex.exp c = 1 := by
      dsimp [c]
      rw [Complex.exp_sub, ← hfA p hp.1, ← hfB p hp.2,
        div_self (hfB p hp.2 ▸ Complex.exp_ne_zero (gB p))]
    refine hasLogOn_union (gA := gA) (gB := fun x => gB x + c) hA hB hgA
      (hgB.add continuousOn_const) hfA
      (fun x hx => by rw [Complex.exp_add, hexpc, mul_one, hfB x hx]) ?_
    intro x hx
    have hxp : x = p := hAB hx hp
    subst hxp
    dsimp [c]
    ring
  · rw [not_nonempty_iff_eq_empty] at hne
    exact hasLogOn_union hA hB hgA hgB hfA hfB (fun x hx => by rw [hne] at hx; exact False.elim hx)

/-- Restricting an embedding by removing an isolated vertex removes only its point from `U`. -/
private theorem U_eq_restrict_union_pt {u : V} (φ : PlaneEmbedding G R) (hu : u ∈ R)
    (hiso : ∀ v ∈ R, ¬ G.Adj u v) :
    φ.U = (φ.restrict (R' := R \ {u}) sdiff_subset).U ∪ {φ.pt u} ∧
      Disjoint (φ.restrict (R' := R \ {u}) sdiff_subset).U {φ.pt u} := by
  set φ' := φ.restrict (R' := R \ {u}) sdiff_subset
  refine ⟨Subset.antisymm (fun z hz => ?_) (union_subset (fun z hz => ?_) ?_),
    disjoint_singleton_right.mpr ?_⟩
  · rcases hz with ⟨x, hx, rfl⟩ | hz
    · by_cases hxu : x = u
      · exact Or.inr (by simp [hxu])
      · exact Or.inl (Or.inl ⟨x, ⟨hx, hxu⟩, rfl⟩)
    · simp only [mem_iUnion] at hz
      obtain ⟨a, ha, b, hb, hab, hz⟩ := hz
      have hau : a ≠ u := fun h => hiso b hb (h ▸ hab)
      have hbu : b ≠ u := fun h => hiso a ha (h ▸ hab.symm)
      exact Or.inl (φ'.line_subset_U ⟨ha, hau⟩ ⟨hb, hbu⟩ hab hz)
  · rcases hz with ⟨x, ⟨hx, _⟩, rfl⟩ | hz
    · exact φ.pt_mem_U hx
    · simp only [mem_iUnion] at hz
      obtain ⟨a, ⟨ha, _⟩, b, ⟨hb, _⟩, hab, hz⟩ := hz
      exact φ.line_subset_U ha hb hab hz
  · rw [singleton_subset_iff]
    exact φ.pt_mem_U hu
  · rintro (⟨x, ⟨hx, hxu⟩, he⟩ | hz)
    · exact hxu (φ.injOn hx hu he)
    · simp only [mem_iUnion] at hz
      obtain ⟨a, ⟨ha, hau⟩, b, ⟨hb, hbu⟩, hab, hz⟩ := hz
      rcases φ.avoid a ha b hb hab u hu hz with rfl | rfl
      · exact hau rfl
      · exact hbu rfl

/-- Restricting an embedding by removing a leaf `u` with unique neighbour `v` removes only
`φ.line u v` from `U`, meeting `(φ.restrict sdiff_subset).U` in `{φ.pt v}`. -/
private theorem U_eq_restrict_union_line {u v : V} (φ : PlaneEmbedding G R) (hu : u ∈ R)
    (hv : v ∈ R) (huv : G.Adj u v) (hleaf : ∀ w ∈ R, G.Adj u w → w = v) :
    φ.U = (φ.restrict (R' := R \ {u}) sdiff_subset).U ∪ φ.line u v ∧
      ((φ.restrict (R' := R \ {u}) sdiff_subset).U ∩ φ.line u v).Subsingleton := by
  set φ' := φ.restrict (R' := R \ {u}) sdiff_subset
  have hsub_rest : φ'.U ⊆ φ.rest u v := by
    rintro z (⟨x, ⟨hx, _⟩, rfl⟩ | hz)
    · exact Or.inl ⟨x, hx, rfl⟩
    · simp only [mem_iUnion] at hz
      obtain ⟨a, ⟨ha, hau⟩, b, ⟨hb, hbu⟩, hab, hz⟩ := hz
      refine Or.inr (mem_iUnion₂.mpr ⟨a, ha,
        mem_iUnion₂.mpr ⟨b, hb, mem_iUnion.mpr ⟨⟨hab, ?_⟩, hz⟩⟩⟩)
      intro he
      rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hau h1
      · exact hbu h2
  have hptu_not : φ.pt u ∉ φ'.U := by
    rintro (⟨x, ⟨hx, hxu⟩, he⟩ | hz)
    · exact hxu (φ.injOn hx hu he)
    · simp only [mem_iUnion] at hz
      obtain ⟨a, ⟨ha, hau⟩, b, ⟨hb, hbu⟩, hab, hz⟩ := hz
      rcases φ.avoid a ha b hb hab u hu hz with h | h
      · exact hau h.symm
      · exact hbu h.symm
  refine ⟨Subset.antisymm (fun z hz => ?_) ?_, ?_⟩
  · rcases hz with ⟨x, hx, hzx⟩ | hz
    · subst hzx
      by_cases hxu : x = u
      · subst hxu
        exact Or.inr (IsLineWithEnds.left_mem (φ.isLine x hu v hv huv))
      · exact Or.inl (Or.inl ⟨x, ⟨hx, hxu⟩, rfl⟩)
    · simp only [mem_iUnion] at hz
      obtain ⟨a, ha, b, hb, hab, hz⟩ := hz
      by_cases hau : a = u
      · subst hau
        have hbv : b = v := hleaf b hb hab
        subst hbv
        exact Or.inr hz
      · by_cases hbu : b = u
        · subst hbu
          have hav : a = v := hleaf a ha hab.symm
          subst hav
          rw [φ.line_comm] at hz
          exact Or.inr hz
        · exact Or.inl (φ'.line_subset_U ⟨ha, hau⟩ ⟨hb, hbu⟩ hab hz)
  · refine union_subset (fun z hz => ?_) (φ.line_subset_U hu hv huv)
    rw [φ.U_eq_rest hu hv huv]
    exact Or.inl (hsub_rest hz)
  · have hinter : φ'.U ∩ φ.line u v ⊆ {φ.pt v} := by
      rintro z ⟨hz1, hz2⟩
      rcases φ.line_inter_rest hu hv huv ⟨hz2, hsub_rest hz1⟩ with h | h
      · exact absurd (h ▸ hz1) hptu_not
      · exact h
    exact subsingleton_singleton.anti hinter

/-- Every nonvanishing continuous function on the drawn set of a cycle-free graph has a continuous
logarithm. -/
private theorem hasLogOn_U_of_acyclic :
    ∀ (n : ℕ) {G : SimpleGraph V} {R : Set V} (φ : PlaneEmbedding G R), R.ncard = n →
      (¬ ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R) →
      ∀ {f : ℂ → ℂ}, ContinuousOn f φ.U → (∀ z ∈ φ.U, f z ≠ 0) → HasLogOn φ.U f := by
  intro n
  induction n with
  | zero =>
    intro G R φ hn _ f _ _
    have hR : R = ∅ := (ncard_eq_zero φ.finite).mp hn
    subst hR
    have hU : φ.U = ∅ := by simp [PlaneEmbedding.U]
    rw [hU]
    exact ⟨0, continuousOn_empty _, by simp⟩
  | succ n ih =>
    intro G R φ hn hacyc f hf hne
    have hRne : R.Nonempty := (ncard_pos φ.finite).mp (by omega)
    obtain ⟨u, hu, hdeg⟩ := exists_deg_le_one_of_acyclic φ.finite hRne hacyc
    let R' := R \ {u}
    let φ' : PlaneEmbedding G R' := φ.restrict sdiff_subset
    have hn' : R'.ncard = n := by
      have := ncard_sdiff_singleton_add_one hu φ.finite
      change R'.ncard + 1 = R.ncard at this
      omega
    have hacyc' : ¬ ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R' :=
      fun ⟨C, hC, hCR'⟩ => hacyc ⟨C, hC, fun x hx => (hCR' x hx).1⟩
    by_cases hadj : ∃ v ∈ R, G.Adj u v
    · obtain ⟨v, hv, huv⟩ := hadj
      obtain ⟨hUeq, hsub⟩ := φ.U_eq_restrict_union_line hu hv huv
        (fun w hw huw => hdeg w hw v hv huw huv)
      have hU' : φ'.U ⊆ φ.U := hUeq ▸ subset_union_left
      have hL : φ.line u v ⊆ φ.U := hUeq ▸ subset_union_right
      have hlog' := ih φ' hn' hacyc' (hf.mono hU') (fun z hz => hne z (hU' hz))
      obtain ⟨homeo, -, -⟩ := φ.isLine u hu v hv huv
      have hlogL := hasLogOn_of_arc homeo (hf.mono hL) (fun z hz => hne z (hL hz))
      rw [hUeq]
      exact hasLogOn_union_of_subsingleton φ'.isClosed_U
        (φ.isLine u hu v hv huv).isCompact.isClosed hsub hlog' hlogL
    · push Not at hadj
      obtain ⟨hUeq, hdisj⟩ := φ.U_eq_restrict_union_pt hu hadj
      have hU' : φ'.U ⊆ φ.U := hUeq ▸ subset_union_left
      have hlog' := ih φ' hn' hacyc' (hf.mono hU') (fun z hz => hne z (hU' hz))
      have hlog_pt : HasLogOn {φ.pt u} f :=
        (hasLogOn_const (hne _ (φ.pt_mem_U hu))).congr (fun z hz => by rw [mem_singleton_iff.mp hz])
      rw [hUeq]
      exact hasLogOn_union_of_subsingleton φ'.isClosed_U isClosed_singleton
        (by rw [hdisj.inter_eq]; exact subsingleton_empty) hlog' hlog_pt

public section

/-- A cycle-free plane embedding has a single face (`φ.faces.ncard = 1`). -/
theorem faces_ncard_of_acyclic (φ : PlaneEmbedding G R)
    (hacyc : ¬ ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R) :
    φ.faces.Subsingleton ∧ φ.faces.Finite ∧ φ.faces.ncard = 1 := by
  have hsub : φ.faces.Subsingleton := by
    rintro f₁ ⟨a, ha, rfl⟩ f₂ ⟨b, hb, rfl⟩
    simp only [mem_sdiff, mem_univ, true_and] at ha hb
    rw [← compl_eq_univ_sdiff]
    refine component_eq_of_hasLogOn φ.isCompact_U ha hb ?_
    refine φ.hasLogOn_U_of_acyclic R.ncard rfl hacyc ?_ ?_
    · refine (continuousOn_id.sub continuousOn_const).div
        (continuousOn_id.sub continuousOn_const) fun z hz h => hb ?_
      rwa [sub_eq_zero.mp h] at hz
    · intro z hz
      refine div_ne_zero (fun h => ha ?_) (fun h => hb ?_)
      · rwa [sub_eq_zero.mp h] at hz
      · rwa [sub_eq_zero.mp h] at hz
  obtain ⟨r, hr, -⟩ := φ.exists_unbounded_face
  have heq : φ.faces = {r} := Subset.antisymm (fun f hf => mem_singleton_iff.mpr (hsub hf hr))
    (singleton_subset_iff.mpr hr)
  exact ⟨hsub, heq ▸ finite_singleton r, by rw [heq, ncard_singleton]⟩

/-! ### Deleting an edge of a plane embedding -/

/-- Deleting an edge `uv` of `G` on `R` gives a plane embedding with drawn set `φ.rest u v`. -/
@[expose] def deleteEdge (φ : PlaneEmbedding G R) (u v : V) :
    PlaneEmbedding (G.deleteEdges {s(u, v)}) R :=
  φ.mono (fun _ _ _ _ h => G.deleteEdges_le _ h) Subset.rfl

private theorem deleteEdge_U (φ : PlaneEmbedding G R) (u v : V) :
    (φ.deleteEdge u v).U = φ.rest u v := by
  ext z
  simp [PlaneEmbedding.U, PlaneEmbedding.rest, deleteEdge, PlaneEmbedding.mono,
    SimpleGraph.deleteEdges_adj]

/-- Deleting an edge `uv` of `G` on `R` merges the faces `f₁, f₂` on the two sides of `φ.line u v`
into a single face `f₀` of `φ.deleteEdge u v`, while keeping all other faces unchanged. -/
theorem faces_deleteEdge (φ : PlaneEmbedding G R) {u v : V} (hu : u ∈ R) (hv : v ∈ R)
    (huv : G.Adj u v) :
    ∃ f₁ ∈ φ.faces, ∃ f₂ ∈ φ.faces, ∃ f₀ ∈ (φ.deleteEdge u v).faces,
      φ.line u v ⊆ frontier f₁ ∧ φ.line u v ⊆ frontier f₂ ∧
      (∀ T : Set ℂ, IsJordanParts T → T ⊆ φ.U → φ.line u v ⊆ T → f₁ ≠ f₂) ∧
      (φ.deleteEdge u v).faces = insert f₀ (φ.faces \ {f₁, f₂}) ∧
      f₀ ∉ φ.faces \ {f₁, f₂} := by
  set φ' := φ.deleteEdge u v
  have hU' : φ'.U = φ.rest u v := φ.deleteEdge_U u v
  have hUsub : φ'.U ⊆ φ.U := by
    rw [hU', φ.U_eq_rest hu hv huv]
    exact subset_union_left
  obtain ⟨f₁, hf₁, f₂, hf₂, hfr₁, hfr₂, honly, hsep⟩ := φ.edge_faces hu hv huv
  obtain ⟨p, hp, hpu, hpv⟩ := exists_inner_point (φ.isLine u hu v hv huv)
  have hpU' : p ∉ φ'.U := by
    rw [hU']
    intro hp'
    rcases φ.line_inter_rest hu hv huv ⟨hp, hp'⟩ with h | h
    · exact hpu h
    · exact hpv h
  obtain ⟨hf₀, hp₀⟩ := φ'.mem_faces_of_notMem hpU'
  set f₀ := connectedComponentIn (univ \ φ'.U) p
  have hf₀open := (φ'.isOpen_of_mem_faces hf₀).1
  have hf₁sub : f₁ ⊆ f₀ := by
    obtain ⟨z, hzf₀, hzf₁⟩ := mem_closure_iff.mp (hfr₁ hp).1 f₀ hf₀open hp₀
    exact φ'.subset_face hf₀ (φ.isOpen_of_mem_faces hf₁).2.1.isPreconnected
      ((φ.isOpen_of_mem_faces hf₁).2.2.trans (compl_subset_compl.mpr hUsub)) hzf₁ hzf₀
  have hf₂sub : f₂ ⊆ f₀ := by
    obtain ⟨z, hzf₀, hzf₂⟩ := mem_closure_iff.mp (hfr₂ hp).1 f₀ hf₀open hp₀
    exact φ'.subset_face hf₀ (φ.isOpen_of_mem_faces hf₂).2.1.isPreconnected
      ((φ.isOpen_of_mem_faces hf₂).2.2.trans (compl_subset_compl.mpr hUsub)) hzf₂ hzf₀
  have hline_cl : φ.line u v ⊆ closure f₀ :=
    (hfr₁.trans frontier_subset_closure).trans (closure_mono hf₁sub)
  refine ⟨f₁, hf₁, f₂, hf₂, f₀, hf₀, hfr₁, hfr₂, hsep,
    Subset.antisymm (fun g hg => ?_) ?_, ?_⟩
  · by_cases hg₀ : g = f₀
    · exact Or.inl hg₀
    · right
      obtain ⟨hgo, hgc, hgU'⟩ := φ'.isOpen_of_mem_faces hg
      have hgL : Disjoint g (φ.line u v) := disjoint_left.mpr fun z hzg hzL => by
        obtain ⟨w, hwg, hwf₀⟩ := mem_closure_iff.mp (hline_cl hzL) g hgo hzg
        exact hg₀ (φ'.eq_of_mem_faces hg hf₀ hwg hwf₀)
      have hgU : g ⊆ φ.Uᶜ := by
        rw [φ.U_eq_rest hu hv huv, ← hU']
        intro z hzg hzU
        rcases hzU with h | h
        · exact hgU' hzg h
        · exact disjoint_left.mp hgL hzg h
      have hfrg : frontier g ⊆ φ.U := by
        intro z hz
        have hz' : z ∈ φ'.U := by
          by_contra hnot
          obtain ⟨h_face, hzh⟩ := φ'.mem_faces_of_notMem hnot
          obtain ⟨w, hwh, hwg⟩ := mem_closure_iff.mp hz.1 _ (φ'.isOpen_of_mem_faces h_face).1 hzh
          have heq := φ'.eq_of_mem_faces hg h_face hwg hwh
          rw [← heq] at hzh
          rw [frontier, hgo.interior_eq] at hz
          exact hz.2 hzh
        exact hUsub hz'
      have hgφ : g ∈ φ.faces := φ.mem_faces_of_frontier hgo hgc hgU hfrg
      refine ⟨hgφ, ?_⟩
      rintro (rfl | rfl)
      · obtain ⟨z, hz⟩ := hgc.nonempty
        exact hg₀ (φ'.eq_of_mem_faces hg hf₀ hz (hf₁sub hz))
      · obtain ⟨z, hz⟩ := hgc.nonempty
        exact hg₀ (φ'.eq_of_mem_faces hg hf₀ hz (hf₂sub hz))
  · rintro g (rfl | ⟨hgφ, hgne⟩)
    · exact hf₀
    · obtain ⟨hgo, hgc, hgU⟩ := φ.isOpen_of_mem_faces hgφ
      have hfrg : frontier g ⊆ φ'.U := by
        intro z hz
        have hzU : z ∈ φ.U := by
          by_contra hnot
          obtain ⟨h_face, hzh⟩ := φ.mem_faces_of_notMem hnot
          obtain ⟨w, hwh, hwg⟩ := mem_closure_iff.mp hz.1 _ (φ.isOpen_of_mem_faces h_face).1 hzh
          have heq := φ.eq_of_mem_faces hgφ h_face hwg hwh
          rw [← heq] at hzh
          rw [frontier, hgo.interior_eq] at hz
          exact hz.2 hzh
        rw [φ.U_eq_rest hu hv huv, ← hU'] at hzU
        rcases hzU with h | h
        · exact h
        · by_cases hzu : z = φ.pt u
          · rw [hzu]; exact φ'.pt_mem_U hu
          · by_cases hzv : z = φ.pt v
            · rw [hzv]; exact φ'.pt_mem_U hv
            · exact absurd (honly g hgφ z h hzu hzv hz.1) hgne
      exact φ'.mem_faces_of_frontier hgo hgc (hgU.trans (compl_subset_compl.mpr hUsub)) hfrg
  · rintro ⟨hf₀φ, -⟩
    exact (φ.isOpen_of_mem_faces hf₀φ).2.2 hp₀ (φ.line_subset_U hu hv huv hp)

/-- Every plane embedding has finitely many faces. -/
theorem faces_finite :
    ∀ (m : ℕ) {G : SimpleGraph V} {R : Set V} (φ : PlaneEmbedding G R),
      (edgesOn G R).ncard = m → φ.faces.Finite := by
  intro m
  induction m with
  | zero =>
    intro G R φ hm
    have hempty : edgesOn G R = ∅ := (ncard_eq_zero (finite_edgesOn φ.finite)).mp hm
    have hacyc : ¬ ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R := by
      rintro ⟨C, hC, hCR⟩
      rcases C with _ | ⟨x, _ | ⟨y, t⟩⟩
      · simp [IsCycleList] at hC
      · simp [IsCycleList] at hC
      · have hadj : G.Adj x y := hC.2.2 (x, y) (by
          rw [zip_rotate_one_cons]
          exact List.mem_cons_self)
        have hmem : s(x, y) ∈ edgesOn G R :=
          mem_edgesOn_iff.mpr ⟨hCR x (by simp), hCR y (by simp), hadj⟩
        rw [hempty] at hmem
        exact hmem
    exact (φ.faces_ncard_of_acyclic hacyc).2.1
  | succ m ih =>
    intro G R φ hm
    have hne : (edgesOn G R).Nonempty := (ncard_pos (finite_edgesOn φ.finite)).mp (by omega)
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨hu, hv, huv⟩ := mem_edgesOn_iff.mp he
      obtain ⟨heq, hnot⟩ := edgesOn_deleteEdges_singleton hu hv huv
      have hm' : (edgesOn (G.deleteEdges {s(u, v)}) R).ncard = m := by
        rw [heq, ncard_insert_of_notMem hnot (finite_edgesOn φ.finite)] at hm
        omega
      have hfin' := ih (φ.deleteEdge u v) hm'
      obtain ⟨f₁, _, f₂, _, f₀, _, _, _, _, hfaces', -⟩ := φ.faces_deleteEdge hu hv huv
      have hsub : φ.faces ⊆ insert f₁ (insert f₂ (φ.faces \ {f₁, f₂})) := by
        intro f hf
        by_cases h1 : f = f₁
        · exact Or.inl h1
        · by_cases h2 : f = f₂
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr ⟨hf, by simp [h1, h2]⟩)
      have hfin_diff : (φ.faces \ {f₁, f₂}).Finite :=
        hfin'.subset (by rw [hfaces']; exact subset_insert _ _)
      exact ((hfin_diff.insert f₂).insert f₁).subset hsub

/-- **Euler's inequality for plane embeddings**: for any plane embedding `φ : PlaneEmbedding G R`
on a nonempty vertex set `R`, `(edgesOn G R).ncard + 2 ≤ R.ncard + φ.faces.ncard`. -/
theorem euler_ineq :
    ∀ (m : ℕ) {G : SimpleGraph V} {R : Set V} (φ : PlaneEmbedding G R),
      R.Nonempty → (edgesOn G R).ncard = m →
      (edgesOn G R).ncard + 2 ≤ R.ncard + φ.faces.ncard := by
  intro m
  induction m with
  | zero =>
    intro G R φ hRne hm
    have hacyc : ¬ ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R := by
      rintro ⟨C, hC, hCR⟩
      rcases C with _ | ⟨x, _ | ⟨y, t⟩⟩
      · simp [IsCycleList] at hC
      · simp [IsCycleList] at hC
      · have hadj : G.Adj x y := hC.2.2 (x, y) (by
          rw [zip_rotate_one_cons]; exact List.mem_cons_self)
        have hmem : s(x, y) ∈ edgesOn G R :=
          mem_edgesOn_iff.mpr ⟨hCR x (by simp), hCR y (by simp), hadj⟩
        have hempty : edgesOn G R = ∅ := (ncard_eq_zero (finite_edgesOn φ.finite)).mp hm
        rw [hempty] at hmem; exact hmem
    have h1 := acyclic_edgesOn_bound (G := G) R.ncard φ.finite rfl hRne hacyc
    have h2 := (φ.faces_ncard_of_acyclic hacyc).2.2
    omega
  | succ m ih =>
    intro G R φ hRne hm
    by_cases hcyc : ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R
    · obtain ⟨C, hC, hCR⟩ := hcyc
      rcases C with _ | ⟨u, _ | ⟨v, t⟩⟩
      · simp [IsCycleList] at hC
      · simp [IsCycleList] at hC
      have hp : (u, v) ∈ (u :: v :: t).zip ((u :: v :: t).rotate 1) := by
        rw [zip_rotate_one_cons]
        exact List.mem_cons_self
      have hu : u ∈ R := hCR u (by simp)
      have hv : v ∈ R := hCR v (by simp)
      have huv : G.Adj u v := hC.2.2 (u, v) hp
      obtain ⟨heq, hnot⟩ := edgesOn_deleteEdges_singleton hu hv huv
      have hm' : (edgesOn (G.deleteEdges {s(u, v)}) R).ncard = m := by
        rw [heq, ncard_insert_of_notMem hnot (finite_edgesOn φ.finite)] at hm
        omega
      obtain ⟨f₁, hf₁, f₂, hf₂, f₀, _, _, _, hsep, hfaces', hnot₀⟩ := φ.faces_deleteEdge hu hv huv
      have hne12 : f₁ ≠ f₂ := by
        refine hsep (φ.cycleImage (u :: v :: t))
          (isJordanParts (φ.isOArc_cycleImage hC hCR).some)
          (φ.cycleImage_subset_U hC hCR) ?_
        exact (φ.line_subset_cycleImage_iff hC hCR hu hv huv).mpr ⟨(u, v), hp, rfl⟩
      have hfin : φ.faces.Finite := φ.faces_finite (m + 1) hm
      have hfin_diff : (φ.faces \ {f₁, f₂}).Finite := hfin.sdiff
      have hcard' : (φ.deleteEdge u v).faces.ncard = (φ.faces \ {f₁, f₂}).ncard + 1 := by
        rw [hfaces', ncard_insert_of_notMem hnot₀ hfin_diff]
      have hins : insert f₁ (insert f₂ (φ.faces \ {f₁, f₂})) = φ.faces := by
        ext f
        simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff]
        constructor
        · rintro (rfl | rfl | ⟨hf, -⟩) <;> assumption
        · intro hf
          by_cases h1 : f = f₁
          · exact Or.inl h1
          · by_cases h2 : f = f₂
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr ⟨hf, not_or.mpr ⟨h1, h2⟩⟩)
      have hcard : φ.faces.ncard = (φ.faces \ {f₁, f₂}).ncard + 2 := by
        calc
          φ.faces.ncard = (insert f₁ (insert f₂ (φ.faces \ {f₁, f₂}))).ncard := by
            rw [hins]
          _ = (insert f₂ (φ.faces \ {f₁, f₂})).ncard + 1 :=
            ncard_insert_of_notMem (by simp [hne12]) (hfin_diff.insert f₂)
          _ = (φ.faces \ {f₁, f₂}).ncard + 2 := by
            rw [ncard_insert_of_notMem (by simp) hfin_diff]
      have hih := ih (φ.deleteEdge u v) hRne hm'
      omega
    · have h1 := acyclic_edgesOn_bound (G := G) R.ncard φ.finite rfl hRne hcyc
      have h2 := (φ.faces_ncard_of_acyclic hcyc).2.2
      omega

end

end GraphMinor.HP25.PlaneEmbedding
