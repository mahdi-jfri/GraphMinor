module

public import GraphMinor.GM08.Section15Assembly

/-!
# Graph Minors VIII, printed (15.1): decompositions of parts of a graft

The assembly in our proof of the printed (15.1) (`Section15PrintedFinal.lean`) glues several
path-decompositions, each of a part of the graft. This file records such a part by its vertex set
`V₀` and edge set `E₀`, and records four junctions: the first, the second, the second to
last and the last. The second and the second to last junctions are the ones between which a train
needs disjoint paths.

`Decomposes.append` glues two parts that meet exactly in a junction, `Decomposes.reverse` reads a
decomposition backwards, and `Decomposes.mem_LKGraftClass` turns a decomposition of the whole
graft into a train.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph

universe u v

variable {α : Type u} {β : Type v}

theorem subOf_mono (G : Graph α β) {V₁ V₂ : Set α} {E₁ E₂ : Set β} (hV : V₁ ⊆ V₂)
    (hE : E₁ ⊆ E₂) : subOf G V₁ E₁ ≤ subOf G V₂ E₂ where
  vertexSet_mono := hV
  isLink_mono e x y h := by
    rw [subOf_isLink] at h ⊢
    exact ⟨hE h.1, h.2.1, hV h.2.2.1, hV h.2.2.2⟩

/-- If every edge of `E₀` is an edge of `G` with its ends in `V₀`, then `E₀` is the edge set of
`subOf G V₀ E₀`. -/
theorem subOf_edgeSet_of_ends (G : Graph α β) {V₀ : Set α} {E₀ : Set β} (hE : E₀ ⊆ E(G))
    (hends : ∀ e ∈ E₀, ∀ x y, G.IsLink e x y → x ∈ V₀) : E(subOf G V₀ E₀) = E₀ := by
  rw [subOf_edgeSet]
  ext e
  refine ⟨fun h => h.1, fun he => ⟨he, ?_⟩⟩
  obtain ⟨x, y, hxy⟩ : ∃ x y, G.IsLink e x y := exists_isLink_of_mem_edgeSet (hE he)
  exact ⟨x, y, hxy, hends e he x y hxy, hends e he y x hxy.symm⟩

theorem subOf_self (G : Graph α β) : subOf G V(G) E(G) = G :=
  (Compatible.of_le (subOf_le G subset_rfl E(G))).ext rfl
    (subOf_edgeSet_of_ends G subset_rfl fun _ _ _ _ h => h.left_mem)

/-- The part of `X` with vertex set `V₀` and edge set `E₀` has a path-decomposition over `𝒜`
whose junctions are, in order, `Y₀`, `Y₀'`, …, `Y₁'`, `Y₁`, and whose inner junctions have `k`
vertices. Here `Y₀'` is the second junction and `Y₁'` the second to last. -/
def Decomposes (𝒜 : Set (Graft α β)) (X : Graft α β) (V₀ : Set α) (E₀ : Set β)
    (Y₀ Y₀' Y₁' Y₁ : Set α) (k : ℕ) : Prop :=
  ∃ Y : Graft α β, Y.G = subOf X.G V₀ E₀ ∧ Y.T = Y₀ ∪ Y₁ ∧
    ∃ D : GraftPathDecomposition 𝒜 Y, D.Yn 0 = Y₀ ∧ D.Yn 1 = Y₀' ∧ D.Yn (D.r - 1) = Y₁' ∧
      D.Yn D.r = Y₁ ∧ ∀ i, 1 ≤ i → i < D.r → (D.Yn i).ncard = k

namespace Decomposes

variable {𝒜 : Set (Graft α β)} {X : Graft α β}

/-- **One piece.** A part that lies in `𝒜`, with roots `Y₀ ∪ Y₁`, decomposes into itself. -/
theorem single {V₀ : Set α} {E₀ : Set β} {Y₀ Y₁ : Set α} (k : ℕ) (hV₀ : V₀ ⊆ V(X.G))
    (hY : Y₀ ∪ Y₁ ⊆ V₀)
    (hm : ∀ h hf, Graft.mk (subOf X.G V₀ E₀) (Y₀ ∪ Y₁) h hf ∈ 𝒜) :
    Decomposes 𝒜 X V₀ E₀ Y₀ Y₁ Y₀ Y₁ k := by
  have hle := subOf_le X.G hV₀ E₀
  let Y : Graft α β := ⟨subOf X.G V₀ E₀, Y₀ ∪ Y₁, hY,
    ⟨X.finite_G.1.subset hle.vertexSet_mono, X.finite_G.2.subset hle.edgeSet_mono⟩⟩
  refine ⟨Y, rfl, rfl, GraftPathDecomposition.single (X := Y) hY (hm _ _) rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact GraftPathDecomposition.single_Yn_zero
  · exact GraftPathDecomposition.single_Yn_one
  · exact GraftPathDecomposition.single_Yn_zero
  · exact GraftPathDecomposition.single_Yn_one
  · intro i h1 h2
    change i < 1 at h2
    omega

/-- **Gluing two parts.** Two parts with no common edge, whose vertex sets meet exactly in the
last junction `J` of the first, which is also the first junction of the second, glue to a
decomposition of their union. The junction `J` becomes an inner junction, so it must have `k`
vertices. -/
theorem append {V₁ V₂ : Set α} {E₁ E₂ : Set β} {Y₀ Y₀' J₁' J J₀' Y₁' Y₁ : Set α} {k : ℕ}
    (h₁ : Decomposes 𝒜 X V₁ E₁ Y₀ Y₀' J₁' J k) (h₂ : Decomposes 𝒜 X V₂ E₂ J J₀' Y₁' Y₁ k)
    (hE₁ : E₁ ⊆ E(X.G)) (hE₂ : E₂ ⊆ E(X.G))
    (hends₁ : ∀ e ∈ E₁, ∀ x y, X.G.IsLink e x y → x ∈ V₁)
    (hends₂ : ∀ e ∈ E₂, ∀ x y, X.G.IsLink e x y → x ∈ V₂)
    (hV : V₁ ∩ V₂ = J) (hdisj : Disjoint E₁ E₂) (hJ : J.ncard = k) :
    Decomposes 𝒜 X (V₁ ∪ V₂) (E₁ ∪ E₂) Y₀ Y₀' Y₁' Y₁ k := by
  obtain ⟨Ya, hYaG, hYaT, Da, ha0, ha1, ha', har, hacard⟩ := h₁
  obtain ⟨Yb, hYbG, hYbT, Db, hb0, hb1, hb', hbr, hbcard⟩ := h₂
  have hna := Da.hr
  have hnb := Db.hr
  have hends : ∀ e ∈ E₁ ∪ E₂, ∀ x y, X.G.IsLink e x y → x ∈ V₁ ∪ V₂ := by
    rintro e (he | he) x y h
    exacts [.inl (hends₁ e he x y h), .inr (hends₂ e he x y h)]
  have hEa : E(Ya.G) = E₁ := by rw [hYaG]; exact subOf_edgeSet_of_ends X.G hE₁ hends₁
  have hEb : E(Yb.G) = E₂ := by rw [hYbG]; exact subOf_edgeSet_of_ends X.G hE₂ hends₂
  have hE : E(subOf X.G (V₁ ∪ V₂) (E₁ ∪ E₂)) = E(Ya.G) ∪ E(Yb.G) := by
    rw [hEa, hEb]
    exact subOf_edgeSet_of_ends X.G (union_subset hE₁ hE₂) hends
  have hVa : V(Ya.G) = V₁ := by rw [hYaG]; rfl
  have hVb : V(Yb.G) = V₂ := by rw [hYbG]; rfl
  have hY₀ : Y₀ ⊆ V₁ := hVa ▸ (hYaT ▸ Ya.T_subset : Y₀ ∪ J ⊆ V(Ya.G)) |>.trans' subset_union_left
  have hY₁ : Y₁ ⊆ V₂ := hVb ▸ (hYbT ▸ Yb.T_subset : J ∪ Y₁ ⊆ V(Yb.G)) |>.trans' subset_union_right
  let Y : Graft α β := ⟨subOf X.G (V₁ ∪ V₂) (E₁ ∪ E₂), Y₀ ∪ Y₁,
    union_subset_union hY₀ hY₁,
    ⟨by rw [subOf_vertexSet, ← hVa, ← hVb]; exact Ya.finite_G.1.union Yb.finite_G.1,
      by rw [hE]; exact Ya.finite_G.2.union Yb.finite_G.2⟩⟩
  have hle₁ : Ya.G ≤ Y.G := by
    rw [hYaG]; exact subOf_mono X.G subset_union_left subset_union_left
  have hle₂ : Yb.G ≤ Y.G := by
    rw [hYbG]; exact subOf_mono X.G subset_union_right subset_union_right
  let D := GraftPathDecomposition.append (X := Y) Da Db hle₁ hle₂
    (by rw [hVa, hVb]; rfl) hE (by rw [hEa, hEb]; exact hdisj)
    (by rw [hVa, hVb, hV, har]) (by rw [hb0, har]) (by rw [ha0, hbr])
  have hDr : D.r = Da.r + Db.r := GraftPathDecomposition.append_r
  refine ⟨Y, rfl, rfl, D, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GraftPathDecomposition.append_Yn_left (Nat.zero_le _), ha0]
  · rw [GraftPathDecomposition.append_Yn_left hna, ha1]
  · rw [hDr, GraftPathDecomposition.append_Yn_right (by omega) (by omega),
      show Da.r + Db.r - 1 - Da.r = Db.r - 1 by omega, hb']
  · rw [hDr, GraftPathDecomposition.append_Yn_right (by omega) le_rfl,
      show Da.r + Db.r - Da.r = Db.r by omega, hbr]
  · intro i h1 h2
    rw [hDr] at h2
    rcases lt_trichotomy i Da.r with hi | rfl | hi
    · rw [GraftPathDecomposition.append_Yn_left hi.le]
      exact hacard i h1 hi
    · rw [GraftPathDecomposition.append_Yn_left le_rfl, har]
      exact hJ
    · rw [GraftPathDecomposition.append_Yn_right hi.le (by omega)]
      exact hbcard _ (by omega) (by omega)

/-- **Reading backwards.** A decomposition read in the opposite order. -/
theorem reverse {V₀ : Set α} {E₀ : Set β} {Y₀ Y₀' Y₁' Y₁ : Set α} {k : ℕ}
    (h : Decomposes 𝒜 X V₀ E₀ Y₀ Y₀' Y₁' Y₁ k) : Decomposes 𝒜 X V₀ E₀ Y₁ Y₁' Y₀' Y₀ k := by
  obtain ⟨Y, hYG, hYT, D, h0, h1, h', hr, hcard⟩ := h
  have hn := D.hr
  refine ⟨Y, hYG, by rw [hYT, union_comm], D.reverse, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GraftPathDecomposition.reverse_Yn (Nat.zero_le _), Nat.sub_zero, hr]
  · rw [GraftPathDecomposition.reverse_Yn hn, h']
  · rw [GraftPathDecomposition.reverse_r, GraftPathDecomposition.reverse_Yn (by omega),
      show D.r - (D.r - 1) = 1 by omega, h1]
  · rw [GraftPathDecomposition.reverse_r, GraftPathDecomposition.reverse_Yn le_rfl, Nat.sub_self,
      h0]
  · intro i h1 h2
    rw [GraftPathDecomposition.reverse_r] at h2
    rw [GraftPathDecomposition.reverse_Yn h2.le]
    exact hcard _ (by omega) (by omega)

/-- Changing the vertex and edge sets to equal ones. -/
theorem congr_sets {V₀ V₀' : Set α} {E₀ E₀' : Set β} {Y₀ Y₀' Y₁' Y₁ : Set α} {k : ℕ}
    (h : Decomposes 𝒜 X V₀ E₀ Y₀ Y₀' Y₁' Y₁ k) (hV : V₀ = V₀') (hE : E₀ = E₀') :
    Decomposes 𝒜 X V₀' E₀' Y₀ Y₀' Y₁' Y₁ k := by
  subst hV hE
  exact h

/-- **The train.** A decomposition of the whole graft, whose first and last junctions make up its
roots, with `k` disjoint paths between its second and its second to last junctions, makes the
graft a `k`-train. -/
theorem mem_LKGraftClass {Y₀ Y₀' Y₁' Y₁ : Set α} {k : ℕ}
    (h : Decomposes 𝒜 X V(X.G) E(X.G) Y₀ Y₀' Y₁' Y₁ k) (hT : X.T = Y₀ ∪ Y₁)
    (hlink : HasDisjointGraphPathsFromTo X.G Y₀' Y₁' k) : X ∈ LKGraftClass k 𝒜 := by
  obtain ⟨Y, hYG, hYT, D, -, h1, h', -, hcard⟩ := h
  have hYX : Y = X := by
    obtain ⟨G, T, hT', hf⟩ := Y
    obtain ⟨G', T', hT'', hf'⟩ := X
    simp only at hYG hYT hT
    rw [subOf_self] at hYG
    subst hYG hYT hT
    rfl
  subst hYX
  refine isKTrain_of_decomposition D hcard fun _ => ?_
  rw [h1, h']
  exact hlink

end Decomposes

/-- `r` one-vertex paths on a set of `r` vertices. -/
theorem hasDisjointGraphPathsFromTo_self (G : Graph α β) {J : Set α} (hJ : J ⊆ V(G))
    (hfin : J.Finite) : HasDisjointGraphPathsFromTo G J J J.ncard := by
  classical
  have : Fintype J := hfin.fintype
  let e : J ≃ Fin J.ncard := (Fintype.equivFinOfCardEq (by rw [ncard_eq_toFinset_card' J,
    Set.toFinset_card]))
  refine ⟨fun p => subOf G {(e.symm p).1} ∅, fun p => ?_, fun p q hpq => ?_⟩
  · refine ⟨(e.symm p).1, (e.symm p).2, (e.symm p).1, (e.symm p).2, ⟨?_⟩⟩
    exact { verts := [(e.symm p).1]
            edges := []
            le_G := subOf_le G (singleton_subset_iff.mpr (hJ (e.symm p).2)) ∅
            length_verts := rfl
            nodup_verts := List.nodup_singleton _
            head_eq := rfl
            last_eq := rfl
            vertexSet_eq := by ext x; simp
            edgeSet_eq := by
              ext x
              rw [subOf_edgeSet]
              simp
            isLink_step := fun s hs => absurd hs (Nat.not_lt_zero _) }
  · rw [subOf_vertexSet, subOf_vertexSet, disjoint_singleton]
    intro h
    exact hpq (e.symm.injective (Subtype.ext h))

end GraphMinor.GM08
