module

public import GraphMinor.GM07.NetExistsMerge
public import GraphMinor.GM19.CutDrawing2
public import GraphMinor.GM19.FeatureDissect
public import GraphMinor.GM19.FeatureCut

/-!
# Cutting a surface along the edges of a drawing

We cut a connected surface along finitely many paths with disjoint insides, which may be closed (`exists_edges_cut`). Since the cut of
`GM19.exists_abstractCut` takes lines, each path is split at its middle point. The lines are put in a dissection only to build the cut
surface, so a vertex that the dissection adds on a path plays no part afterwards. The lifts of the two halves are then joined by
`exists_merged_cut`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

local notation "𝕀" => unitInterval

universe u

/-- The parameter of a half of a path. -/
noncomputable def halfW (b : Bool) (x : ℝ) : ℝ := if b then x / 2 else (1 + x) / 2

theorem halfW_mem (b : Bool) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : halfW b x ∈ Icc (0 : ℝ) 1 := by
  cases b <;> simp only [halfW, if_true, if_false, Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith [hx.1, hx.2]

theorem halfW_Ioo (b : Bool) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : halfW b x ∈ Ioo (0 : ℝ) 1 ∧ halfW b x ≠ 1 / 2 := by
  cases b <;> simp only [halfW, Bool.false_eq_true, ↓reduceIte] <;> refine ⟨⟨?_, ?_⟩, ?_⟩ <;> first | linarith [hx.1, hx.2] | (intro h; linarith [hx.1, hx.2])

theorem halfW_inj {b b' : Bool} {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) (h : halfW b x = halfW b' y) : b = b' ∧ x = y := by
  have h1 := hx.1
  have h2 := hx.2
  have h3 := hy.1
  have h4 := hy.2
  cases b <;> cases b' <;> simp only [halfW, Bool.false_eq_true, ↓reduceIte] at h
  · exact ⟨rfl, by linarith⟩
  · linarith
  · linarith
  · exact ⟨rfl, by linarith⟩

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {E : Type u} [Finite E] {P : Set S} {c : E → ℝ → S}

/-- **The cut along a family of paths, with the boundary pieces.** Let `c e` be paths with ends in `P`, with insides off `P`, off the
boundary and disjoint. Then the surface can be cut along them and along finitely many paths `b r` of its boundary, which cover the
boundary. The paths `c e` are the inner paths of the cut, and the paths `b r` are not. -/
theorem exists_edges_cut_sum (hS : IsSurface S) (cc : ∀ e, Continuous (c e)) (hinj : ∀ e, InjOn (c e) (Ioo 0 1)) (h0 : ∀ e, c e 0 ∈ P) (h1 : ∀ e, c e 1 ∈ P)
    (hoff : ∀ e, ∀ u ∈ Ioo (0 : ℝ) 1, c e u ∉ P) (hdis : ∀ e e', e ≠ e' → ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1, c e u ≠ c e' v)
    (hbd : ∀ e, ∀ u ∈ Ioo (0 : ℝ) 1, c e u ∉ bd S) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (R : Type u) (_ : Finite R) (b : R → ℝ → S) (ψ : Y → S) (ξ η : E ⊕ R → ℝ → Y),
      IsSurface Y ∧ IsNetCut (Sum.elim c b) (Sum.elim (fun _ => True) fun _ => False) ψ ξ η ∧
      (∀ r, ∀ u ∈ Icc (0 : ℝ) 1, b r u ∈ bd S) ∧ ∀ x ∈ bd S, ∃ k, ∃ u ∈ Icc (0 : ℝ) 1, Sum.elim c b k u = x := by
  classical
  have hh : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have w0t : halfW true 0 = 0 := by simp [halfW]
  have w1t : halfW true 1 = 1 / 2 := by simp [halfW]
  have w0f : halfW false 0 = 1 / 2 := by simp [halfW]
  have w1f : halfW false 1 = 1 := by simp [halfW]
  set A : E × Bool → 𝕀 → S := fun i x => c i.1 (halfW i.2 x) with hA
  have hAc : ∀ i, Continuous (A i) := fun i => by
    obtain ⟨e, b⟩ := i
    cases b <;> simp only [hA, halfW, Bool.false_eq_true, ↓reduceIte]
    · exact (cc e).comp (by fun_prop)
    · exact (cc e).comp (by fun_prop)
  set N : Set S := ⋃ e, {c e 0, c e 1, c e (1 / 2)} with hN
  have hNfin : N.Finite := finite_iUnion fun e => by simp
  have hmemN : ∀ e, c e 0 ∈ N ∧ c e 1 ∈ N ∧ c e (1 / 2) ∈ N := fun e => by
    refine ⟨mem_iUnion.mpr ⟨e, by simp⟩, mem_iUnion.mpr ⟨e, by simp⟩, mem_iUnion.mpr ⟨e, by simp⟩⟩
  have hend : ∀ (x : 𝕀), (x : ℝ) ∉ Ioo (0 : ℝ) 1 → x = 0 ∨ x = 1 := fun x hx => by
    by_cases h2 : (x : ℝ) = 0
    · exact .inl (Subtype.ext h2)
    · right
      refine Subtype.ext ?_
      by_contra h3
      exact hx ⟨lt_of_le_of_ne x.2.1 (Ne.symm h2), lt_of_le_of_ne x.2.2 h3⟩
  have hN1 : ∀ i (x : 𝕀), (x : ℝ) ∉ Ioo (0 : ℝ) 1 → A i x ∈ N := by
    rintro ⟨e, b⟩ x hx
    rcases hend x hx with rfl | rfl <;> cases b <;> simp only [hA, Icc.coe_zero, Icc.coe_one, w0t, w1t, w0f, w1f]
    · exact (hmemN e).2.2
    · exact (hmemN e).1
    · exact (hmemN e).2.1
    · exact (hmemN e).2.2
  have hN2 : ∀ i (x : 𝕀), (x : ℝ) ∈ Ioo (0 : ℝ) 1 → A i x ∉ N := by
    rintro ⟨e, b⟩ x hx hmem
    obtain ⟨h2, h3⟩ := halfW_Ioo b hx
    obtain ⟨e', he⟩ := mem_iUnion.mp hmem
    simp only [mem_insert_iff, mem_singleton_iff, hA] at he
    rcases he with he | he | he
    · exact hoff e _ h2 (he ▸ h0 e')
    · exact hoff e _ h2 (he ▸ h1 e')
    · by_cases hee : e = e'
      · subst hee
        exact h3 (hinj e h2 hh he)
      · exact hdis e e' hee _ h2 _ hh he
  have hmid : ∀ e, c e (1 / 2) ∉ P := fun e => hoff e _ hh
  have hAends : ∀ i, A i 0 ≠ A i 1 := by
    rintro ⟨e, b⟩ he
    cases b <;> simp only [hA, Icc.coe_zero, Icc.coe_one, w0t, w1t, w0f, w1f] at he
    · exact hmid e (he ▸ h1 e)
    · exact hmid e (he.symm ▸ h0 e)
  have hAinj : ∀ i, Function.Injective (A i) := by
    rintro ⟨e, b⟩ x y he
    by_cases hx : (x : ℝ) ∈ Ioo (0 : ℝ) 1 <;> by_cases hy : (y : ℝ) ∈ Ioo (0 : ℝ) 1
    · exact Subtype.ext (halfW_inj hx hy (hinj e (halfW_Ioo b hx).1 (halfW_Ioo b hy).1 he)).2
    · exact absurd (he ▸ hN1 (e, b) y hy) (hN2 (e, b) x hx)
    · exact absurd (he.symm ▸ hN1 (e, b) x hx) (hN2 (e, b) y hy)
    · rcases hend x hx with rfl | rfl <;> rcases hend y hy with rfl | rfl
      · rfl
      · exact absurd he (hAends _)
      · exact absurd he.symm (hAends _)
      · rfl
  have hAarc : ∀ i, IsArcMap (A i) := fun i => ⟨hAc i, hAinj i⟩
  have hnearr : ∀ i j (x y : 𝕀), A i x = A j y → (x : ℝ) ∈ Ioo (0 : ℝ) 1 → (y : ℝ) ∈ Ioo (0 : ℝ) 1 → i = j := by
    rintro ⟨e, b⟩ ⟨e', b'⟩ x y he hx hy
    obtain rfl : e = e' := by
      by_contra hee
      exact hdis e e' hee _ (halfW_Ioo b hx).1 _ (halfW_Ioo b' hy).1 he
    obtain ⟨rfl, -⟩ := halfW_inj hx hy (hinj e (halfW_Ioo b hx).1 (halfW_Ioo b' hy).1 he)
    rfl
  set hp : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩ with hhp
  have hrinj : ∀ i j, range (A i) = range (A j) → i = j := fun i j he => by
    obtain ⟨y, hy⟩ : A i hp ∈ range (A j) := he ▸ mem_range_self _
    by_cases hy' : (y : ℝ) ∈ Ioo (0 : ℝ) 1
    · exact hnearr i j hp y hy.symm hh hy'
    · exact absurd (hy ▸ hN1 j y hy') (hN2 i hp hh)
  set 𝓔 : Set (Set S) := range fun i => range (A i) with h𝓔
  have hline : ∀ L ∈ 𝓔, ∃ u v, u ≠ v ∧ IsLineWithEnds L u v ∧ L ∩ N = {u, v} := by
    rintro _ ⟨i, rfl⟩
    refine ⟨_, _, hAends i, (hAarc i).isLineWithEnds, ?_⟩
    ext y
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨x, rfl⟩, hy⟩
      by_cases hx : (x : ℝ) ∈ Ioo (0 : ℝ) 1
      · exact absurd hy (hN2 i x hx)
      · rcases hend x hx with rfl | rfl
        · exact .inl rfl
        · exact .inr rfl
    · rintro (rfl | rfl)
      · exact ⟨mem_range_self _, hN1 i 0 (by simp)⟩
      · exact ⟨mem_range_self _, hN1 i 1 (by simp)⟩
  have hdisj : ∀ L ∈ 𝓔, ∀ L' ∈ 𝓔, L ≠ L' → L ∩ L' ⊆ N := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne y ⟨⟨x, rfl⟩, ⟨x', hx'⟩⟩
    by_contra hy
    have hx : (x : ℝ) ∈ Ioo (0 : ℝ) 1 := by
      by_contra h2
      exact hy (hN1 i x h2)
    have hx2 : (x' : ℝ) ∈ Ioo (0 : ℝ) 1 := by
      by_contra h2
      exact hy (hx' ▸ hN1 j x' h2)
    exact hne (by rw [hnearr i j x x' hx'.symm hx hx2])
  have hAbd : ∀ i (x : 𝕀), (x : ℝ) ∈ Ioo (0 : ℝ) 1 → A i x ∉ bd S := fun i x hx => hbd i.1 _ (halfW_Ioo i.2 hx).1
  have hbd' : ∀ L ∈ 𝓔, L ∩ bd S ⊆ N := by
    rintro _ ⟨i, rfl⟩ y ⟨⟨x, rfl⟩, hy⟩
    by_contra hn
    refine hAbd i x ?_ hy
    by_contra h2
    exact hn (hN1 i x h2)
  have hNs : N ⊆ bd S ∪ ⋃₀ 𝓔 := by
    intro y hy
    obtain ⟨e, he⟩ := mem_iUnion.mp hy
    simp only [mem_insert_iff, mem_singleton_iff] at he
    refine .inr ?_
    rcases he with rfl | rfl | rfl
    · refine ⟨_, ⟨(e, true), rfl⟩, 0, ?_⟩
      simp [hA, w0t]
    · refine ⟨_, ⟨(e, false), rfl⟩, 1, ?_⟩
      simp [hA, w1f]
    · refine ⟨_, ⟨(e, true), rfl⟩, 1, ?_⟩
      simp [hA, w1t]
  obtain ⟨V, E', hNV, hg, hVE, hU, hsub⟩ := GM19.exists_graph_of_lines hS hNfin (Set.finite_range _) hline hdisj hbd' hNs
  obtain ⟨V₂, E₂, 𝓕, hd, hV₂, hgr⟩ := GM19.exists_dissection_graph hS hg hVE (by rw [hU]; exact subset_union_left)
  set R := {L : Set S // L ∈ E' ∧ L ∉ 𝓔} with hR
  haveI : Finite R := (hg.fine.subset fun L hL => hL.1).to_subtype
  have hrep : ∀ r : R, ∃ a : 𝕀 → S, IsArcMap a ∧ range a = r.1 ∧ r.1 ∩ V = {a 0, a 1} := fun r => by
    obtain ⟨u, v, -, hl, hcap⟩ := hg.edge r.1 r.2.1
    obtain ⟨a, ha, h2, rfl, rfl⟩ := hl.exists_arc
    exact ⟨a, ha, h2, hcap⟩
  choose B hBa hBr hBc using hrep
  set b : (E × Bool) ⊕ R → 𝕀 → S := Sum.elim A B with hb
  have hbarc : ∀ k, IsArcMap (b k) := by
    rintro (i | r)
    · exact hAarc i
    · exact hBa r
  have hbE : ∀ k, range (b k) ∈ E' := by
    rintro (i | r)
    · exact hsub ⟨i, rfl⟩
    · change range (B r) ∈ E'
      rw [hBr r]
      exact r.2.1
  have hbcap : ∀ k, ∀ y ∈ range (b k) ∩ V, y = b k 0 ∨ y = b k 1 := by
    rintro (i | r) y hy
    · obtain ⟨u, v, -, -, hcap⟩ := hg.edge _ (hbE (.inl i))
      have h3 : A i 0 ∈ ({u, v} : Set S) := hcap ▸ ⟨mem_range_self _, hNV (hN1 i 0 (by simp))⟩
      have h4 : A i 1 ∈ ({u, v} : Set S) := hcap ▸ ⟨mem_range_self _, hNV (hN1 i 1 (by simp))⟩
      have h5 : y ∈ ({u, v} : Set S) := hcap ▸ hy
      simp only [mem_insert_iff, mem_singleton_iff] at h3 h4 h5
      change y = A i 0 ∨ y = A i 1
      rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;>
        first
          | exact .inl (h5.trans h3.symm)
          | exact .inr (h5.trans h4.symm)
          | exact absurd (h3.trans h4.symm) (hAends i)
    · have h3 : y ∈ r.1 ∩ V := by
        have h4 : y ∈ range (B r) ∩ V := hy
        rwa [hBr r] at h4
      rw [hBc r] at h3
      exact h3
  have hbinj : ∀ k k', range (b k) = range (b k') → k = k' := by
    rintro (i | r) (j | r') he
    · rw [hrinj i j he]
    · have h2 : range (A i) = r'.1 := (show range (A i) = range (B r') from he).trans (hBr r')
      exact absurd ⟨i, h2⟩ r'.2.2
    · have h2 : range (A j) = r.1 := (show range (A j) = range (B r) from he.symm).trans (hBr r)
      exact absurd ⟨j, h2⟩ r.2.2
    · have h2 : r.1 = r'.1 := (hBr r).symm.trans ((show range (B r) = range (B r') from he).trans (hBr r'))
      rw [Subtype.ext h2]
  have hbV : ∀ k, b k 0 ∈ V ∧ b k 1 ∈ V := by
    rintro (i | r)
    · exact ⟨hNV (hN1 i 0 (by simp)), hNV (hN1 i 1 (by simp))⟩
    · have h2 := hBc r
      have h3 : B r 0 ∈ r.1 ∩ V := by rw [h2]; simp
      have h4 : B r 1 ∈ r.1 ∩ V := by rw [h2]; simp
      exact ⟨h3.2, h4.2⟩
  have hinter : ∀ k (x : 𝕀), (x : ℝ) ∈ Ioo (0 : ℝ) 1 → b k x ∉ V := by
    intro k x hx hV
    rcases hbcap k _ ⟨mem_range_self _, hV⟩ with h2 | h2
    · have h3 := (hbarc k).2 h2
      rw [h3] at hx
      simp at hx
    · have h3 := (hbarc k).2 h2
      rw [h3] at hx
      simp at hx
  have hmeet₀ : ∀ k k' (x y : 𝕀), b k x = b k' y → (k = k' ∧ x = y) ∨ ((x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1)) := by
    intro k k' x y he
    by_cases hk : k = k'
    · subst hk
      exact .inl ⟨rfl, (hbarc k).2 he⟩
    · have h2 : b k x ∈ V := hg.disj _ (hbE k) _ (hbE k') (fun h3 => hk (hbinj _ _ h3)) ⟨mem_range_self _, ⟨y, he.symm⟩⟩
      have h3 : b k' y ∈ V := he ▸ h2
      refine .inr ⟨(hbcap k _ ⟨mem_range_self _, h2⟩).imp (fun h4 => (hbarc k).2 h4) (fun h4 => (hbarc k).2 h4),
        (hbcap k' _ ⟨mem_range_self _, h3⟩).imp (fun h4 => (hbarc k').2 h4) (fun h4 => (hbarc k').2 h4)⟩
  have hon : ∀ r : R, ∀ u ∈ Icc (0 : ℝ) 1, extI (B r) u ∈ bd S := by
    intro r
    refine GM19.mem_of_Ioo (isClosed_bd S) (continuous_extI (hBa r).1).continuousOn fun u hu => ?_
    have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    have h2 : B r ⟨u, hu'⟩ ∈ ⋃₀ E' := ⟨r.1, r.2.1, hBr r ▸ mem_range_self _⟩
    rw [hU] at h2
    rcases h2 with h2 | ⟨_, ⟨i, rfl⟩, ⟨x, hx⟩⟩
    · rw [extI_of_mem _ hu']
      exact h2
    · rcases hmeet₀ (.inr r) (.inl i) ⟨u, hu'⟩ x hx.symm with ⟨h3, -⟩ | ⟨h3, -⟩
      · exact absurd h3 (by simp)
      · rcases h3 with h3 | h3
        · have := congrArg Subtype.val h3
          simp only [Icc.coe_zero] at this
          exact absurd this hu.1.ne'
        · have := congrArg Subtype.val h3
          simp only [Icc.coe_one] at this
          exact absurd this hu.2.ne
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin ((E × Bool) ⊕ R)
  set inner₀ : (E × Bool) ⊕ R → Prop := Sum.elim (fun _ => True) (fun _ => False) with hinner₀
  have hsym : ∀ k, φ.symm (φ k) = k := φ.symm_apply_apply
  have hbext : ∀ k, ∀ u (hu : u ∈ Icc (0 : ℝ) 1), extI (b k) u = b k ⟨u, hu⟩ := fun k u hu => extI_of_mem _ hu
  have hIoo : ∀ {u : ℝ}, u ∈ Ioo (0 : ℝ) 1 → u ∈ Icc (0 : ℝ) 1 := fun hu => ⟨hu.1.le, hu.2.le⟩
  have hL : GM19.IsLineFamily (fun j : Fin n => b (φ.symm j)) (fun j => inner₀ (φ.symm j)) := by
    refine ⟨fun j => hbarc _, fun i j u v hu hv he => ?_, fun j hj u hu => ?_, fun j hj u hu => ?_, fun x hx => ?_⟩
    · rw [hbext _ u hu, hbext _ v hv] at he
      rcases hmeet₀ _ _ _ _ he with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact .inl ⟨φ.symm.injective h2, congrArg Subtype.val h3⟩
      · exact .inr ⟨h2.imp (congrArg Subtype.val) (congrArg Subtype.val), h3.imp (congrArg Subtype.val) (congrArg Subtype.val)⟩
    · generalize φ.symm j = k at hj
      rcases k with i | r
      · change extI (A i) u ∉ bd S
        rw [extI_of_mem _ (hIoo hu)]
        exact hAbd i ⟨u, hIoo hu⟩ hu
      · exact absurd hj (by simp [hinner₀])
    · generalize φ.symm j = k at hj
      rcases k with i | r
      · exact absurd (by simp [hinner₀]) hj
      · exact hon r u hu
    · have h2 : x ∈ ⋃₀ E' := by
        rw [hU]
        exact .inl hx
      obtain ⟨L, hL, hxL⟩ := h2
      by_cases h3 : L ∈ 𝓔
      · obtain ⟨i, rfl⟩ := h3
        obtain ⟨y, rfl⟩ := hxL
        exact ⟨φ (.inl i), by rw [hsym]; exact ⟨y, rfl⟩⟩
      · have hr : L ∈ E' ∧ L ∉ 𝓔 := ⟨hL, h3⟩
        refine ⟨φ (.inr ⟨L, hr⟩), ?_⟩
        rw [hsym]
        change x ∈ range (B ⟨L, hr⟩)
        rw [hBr]
        exact hxL
  obtain ⟨Y, t1, t2, ψ, ξ', η', hY, hC⟩ := GM19.exists_abstractCut hS hL hd (fun j => ⟨hV₂ (hbV _).1, hV₂ (hbV _).2⟩)
    fun j => (subset_sUnion_of_mem (hbE _)).trans hgr
  set a₀ : (E × Bool) ⊕ R → ℝ → S := fun k => extI (b k) with ha₀
  set ξ : (E × Bool) ⊕ R → ℝ → Y := fun k => ξ' (φ k) with hξ
  set η : (E × Bool) ⊕ R → ℝ → Y := fun k => η' (φ k) with hη
  have hξ' : ∀ j, ξ' j = ξ (φ.symm j) := fun j => by simp [hξ]
  have hη' : ∀ j, η' j = η (φ.symm j) := fun j => by simp [hη]
  have h₀ : IsNetCut a₀ (Sum.elim (fun _ => True) fun _ => False) ψ ξ η := by
    refine ⟨hC.cont, hC.surj, fun k => hC.cξ _, fun k => hC.cη _, fun k u hu => ?_, fun k u hu => ?_, fun k u hu => hC.bdξ _ u hu, fun k u hu => hC.bdη _ u hu,
      fun k hk u hu => hC.ne (φ k) (by simpa [hsym] using hk) u hu, fun k hk u hu => hC.eqb (φ k) (by simpa [hsym] using hk) u hu, fun y hy => ?_, fun y y' he => ?_,
      fun k => (extI_injOn (hbarc k).2).mono Ioo_subset_Icc_self, fun k k' hne u hu v hv he => ?_, fun k u hu => ⟨fun he => ?_, fun he => ?_⟩⟩
    · have := hC.hξ (φ k) u hu
      simpa only [hsym] using this
    · have := hC.hη (φ k) u hu
      simpa only [hsym] using this
    · obtain ⟨j, u, hu, h2⟩ := hC.cover y hy
      exact ⟨φ.symm j, u, hu, by rw [← hξ', ← hη']; exact h2⟩
    · have hr := hC.fib y y' he
      clear he
      induction hr with
      | rel p q hs =>
        obtain ⟨j, u, hu, rfl, rfl⟩ := hs
        exact .rel _ _ ⟨φ.symm j, u, hu, by rw [hξ'], by rw [hη']⟩
      | refl _ => exact .refl _
      | symm _ _ _ ih => exact .symm _ _ ih
      | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2
    · simp only [ha₀] at he
      rw [hbext k u (hIoo hu), hbext k' v hv] at he
      rcases hmeet₀ _ _ _ _ he with ⟨h2, -⟩ | ⟨h2, -⟩
      · exact hne h2
      · rcases h2 with h2 | h2
        · exact hu.1.ne' (congrArg Subtype.val h2)
        · exact hu.2.ne (congrArg Subtype.val h2)
    · have := extI_injOn (hbarc k).2 (hIoo hu) (by simp) he
      exact hu.1.ne' this
    · have := extI_injOn (hbarc k).2 (hIoo hu) (by simp) he
      exact hu.2.ne this
  have hex : ∃ ξ' η' : E ⊕ R → ℝ → Y, IsNetCut (Sum.elim c fun r => extI (B r)) (Sum.elim (fun _ => True) fun _ => False) ψ ξ' η' := by
    refine exists_merged_cut h₀ hY ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro e u hu
      exact (extI_of_mem _ hu).trans (by change c e (halfW true u) = c e (u / 2); simp [halfW])
    · intro e u hu
      exact (extI_of_mem _ hu).trans (by change c e (halfW false u) = c e ((1 + u) / 2); simp [halfW])
    · intro r u hu
      rfl
    · intro e k v hv
      constructor
      · intro he
        rcases k with ⟨e', b'⟩ | r
        · have h2 : c e' (halfW b' v) = c e (1 / 2) := by
            have h3 := extI_of_mem (A (e', b')) hv
            exact h3.symm.trans he
          by_cases hvI : v ∈ Ioo (0 : ℝ) 1
          · obtain ⟨h3, h4⟩ := halfW_Ioo b' hvI
            by_cases hee : e' = e
            · subst hee
              exact absurd (hinj e' h3 hh h2) h4
            · exact absurd h2 (hdis e' e hee _ h3 _ hh)
          · obtain rfl | rfl : v = 0 ∨ v = 1 := by
              by_contra hcon
              push Not at hcon
              exact hvI ⟨lt_of_le_of_ne hv.1 (Ne.symm hcon.1), lt_of_le_of_ne hv.2 hcon.2⟩
            · cases b'
              · rw [w0f] at h2
                obtain rfl : e' = e := by
                  by_contra hee
                  exact hdis e' e hee _ hh _ hh h2
                exact .inr ⟨rfl, rfl⟩
              · rw [w0t] at h2
                exact absurd (h2 ▸ h0 e') (hmid e)
            · cases b'
              · rw [w1f] at h2
                exact absurd (h2 ▸ h1 e') (hmid e)
              · rw [w1t] at h2
                obtain rfl : e' = e := by
                  by_contra hee
                  exact hdis e' e hee _ hh _ hh h2
                exact .inl ⟨rfl, rfl⟩
        · have he' : extI (B r) v = c e (1 / 2) := he
          exact absurd (he' ▸ hon r v hv) (hbd e _ hh)
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact (extI_of_mem _ hv).trans (by change c e (halfW true 1) = _; rw [w1t]; rfl)
        · exact (extI_of_mem _ hv).trans (by change c e (halfW false 0) = _; rw [w0f]; rfl)
    · rintro (e | r)
      · exact hinj e
      · exact (extI_injOn (hBa r).2).mono Ioo_subset_Icc_self
    · rintro (e | r) (e' | r') hne u hu v hv he
      · simp only [Sum.elim_inl] at he
        have hee : e ≠ e' := fun h2 => hne (by rw [h2])
        by_cases hvI : v ∈ Ioo (0 : ℝ) 1
        · exact hdis e e' hee u hu v hvI he
        · obtain rfl | rfl : v = 0 ∨ v = 1 := by
            by_contra hcon
            push Not at hcon
            exact hvI ⟨lt_of_le_of_ne hv.1 (Ne.symm hcon.1), lt_of_le_of_ne hv.2 hcon.2⟩
          · exact hoff e u hu (he ▸ h0 e')
          · exact hoff e u hu (he ▸ h1 e')
      · have he' : c e u = extI (B r') v := he
        exact hbd e u hu (he' ▸ hon r' v hv)
      · have he' : extI (B r) u = c e' v := he
        by_cases hvI : v ∈ Ioo (0 : ℝ) 1
        · exact hbd e' v hvI (he' ▸ hon r u (hIoo hu))
        · obtain rfl | rfl : v = 0 ∨ v = 1 := by
            by_contra hcon
            push Not at hcon
            exact hvI ⟨lt_of_le_of_ne hv.1 (Ne.symm hcon.1), lt_of_le_of_ne hv.2 hcon.2⟩
          · refine hinter (.inr r) ⟨u, hIoo hu⟩ hu ?_
            have h2 : B r ⟨u, hIoo hu⟩ = c e' 0 := (extI_of_mem _ (hIoo hu)).symm.trans he'
            change B r ⟨u, hIoo hu⟩ ∈ V
            rw [h2]
            exact hNV (hmemN e').1
          · refine hinter (.inr r) ⟨u, hIoo hu⟩ hu ?_
            have h2 : B r ⟨u, hIoo hu⟩ = c e' 1 := (extI_of_mem _ (hIoo hu)).symm.trans he'
            change B r ⟨u, hIoo hu⟩ ∈ V
            rw [h2]
            exact hNV (hmemN e').2.1
      · have he' : b (.inr r) ⟨u, hIoo hu⟩ = b (.inr r') ⟨v, hv⟩ :=
          (extI_of_mem _ (hIoo hu)).symm.trans (he.trans (extI_of_mem _ hv))
        rcases hmeet₀ _ _ _ _ he' with ⟨h2, -⟩ | ⟨h2, -⟩
        · exact hne (by simpa using h2)
        · rcases h2 with h2 | h2
          · exact hu.1.ne' (congrArg Subtype.val h2)
          · exact hu.2.ne (congrArg Subtype.val h2)
    · rintro (e | r) u hu
      · refine ⟨fun he => ?_, fun he => ?_⟩
        · have he' : c e u = c e 0 := he
          exact hoff e u hu (he' ▸ h0 e)
        · have he' : c e u = c e 1 := he
          exact hoff e u hu (he' ▸ h1 e)
      · exact ⟨fun he => hu.1.ne' (extI_injOn (hBa r).2 (hIoo hu) (by simp) he), fun he => hu.2.ne (extI_injOn (hBa r).2 (hIoo hu) (by simp) he)⟩
  obtain ⟨ξ₁, η₁, hcut⟩ := hex
  refine ⟨Y, t1, t2, R, inferInstance, _, ψ, ξ₁, η₁, hY, hcut, hon, fun x hx => ?_⟩
  have h2 : x ∈ ⋃₀ E' := by
    rw [hU]
    exact .inl hx
  obtain ⟨L, hL, hxL⟩ := h2
  by_cases h3 : L ∈ 𝓔
  · obtain ⟨⟨e, b'⟩, rfl⟩ := h3
    obtain ⟨y, rfl⟩ := hxL
    exact ⟨.inl e, halfW b' y, halfW_mem b' y.2, rfl⟩
  · have hr : L ∈ E' ∧ L ∉ 𝓔 := ⟨hL, h3⟩
    have h4 : x ∈ range (B ⟨L, hr⟩) := by
      rw [hBr]
      exact hxL
    obtain ⟨y, rfl⟩ := h4
    exact ⟨.inr ⟨L, hr⟩, y, y.2, extI_of_mem _ y.2⟩

/-- **The cut along a family of paths.** Let `c e` be paths with ends in `P`, with insides off `P`, off the boundary and disjoint. Then the
surface can be cut along them and along its boundary. The paths are inner paths of the cut. -/
theorem exists_edges_cut (hS : IsSurface S) (cc : ∀ e, Continuous (c e)) (hinj : ∀ e, InjOn (c e) (Ioo 0 1)) (h0 : ∀ e, c e 0 ∈ P) (h1 : ∀ e, c e 1 ∈ P)
    (hoff : ∀ e, ∀ u ∈ Ioo (0 : ℝ) 1, c e u ∉ P) (hdis : ∀ e e', e ≠ e' → ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1, c e u ≠ c e' v)
    (hbd : ∀ e, ∀ u ∈ Ioo (0 : ℝ) 1, c e u ∉ bd S) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (κ : Type u) (_ : Finite κ) (a : κ → ℝ → S) (inner : κ → Prop) (ψ : Y → S) (ξ η : κ → ℝ → Y),
      IsSurface Y ∧ IsNetCut a inner ψ ξ η ∧ ∀ e, ∃ k, inner k ∧ ∀ u ∈ Ioo (0 : ℝ) 1, a k u = c e u := by
  obtain ⟨Y, t1, t2, R, _, b, ψ, ξ, η, hY, hcut, -, -⟩ := exists_edges_cut_sum hS cc hinj h0 h1 hoff hdis hbd
  exact ⟨Y, t1, t2, E ⊕ R, inferInstance, _, _, ψ, ξ, η, hY, hcut, fun e => ⟨.inl e, trivial, fun u _ => rfl⟩⟩

end GraphMinor.GM07
