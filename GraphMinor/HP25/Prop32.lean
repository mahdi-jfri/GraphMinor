module

public import GraphMinor.HP25.Rib
public import GraphMinor.HP25.WebPath
import GraphMinor.Surface.PlaneDisc
import GraphMinor.Surface.Crossing
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.SurfaceGraph

/-!
# Proposition 3.2: frames of webs are crossless

Humeau and Pous, arXiv:2505.16431v2, Proposition 3.2 (page 9): "Frames of webs are crossless."

The paper's proof: "Suppose by contradiction that the frame of a web is crossed. The union of the
frame and the paths from a crossing yields a topological $K_4$. By intersecting paths with the rib,
we can assume a topological $K_4$ in the rib. In a planar embedding of the rib in which the frame
bounds the outer face, this provides an outerplanar plane embedding of $K_4$, a contradiction."

We follow it, with the outerplanarity of `K₄` replaced by the library's crossing lemma for a closed
disc (`Surface.disc_crossing`), which is the topological fact behind it.
1. By Section 3.4 (`WebData.exists_rib_path`) the two paths of a crossing can be taken in the rib.
2. In a plane embedding of the rib with the faces of a rib, the drawing lies in the closed inner
   domain `D` of the image `F` of the frame (`IsRibEmbedding.disjoint_outer`). By the Schoenflies
   theorem `D` is a closed disc with boundary `F` (`Surface.isClosedDisc_closedInner`).
3. The images of the two paths are disjoint lines in `D`. Their ends alternate on `F`: the two ends
   of the first path cut `F` into two arcs (`PlaneEmbedding.cycleImage_split`), and the ends of the
   second path lie on different arcs.
4. Two disjoint compact connected sets in a closed disc cannot join two pairs of points that
   alternate on the boundary (`Surface.disc_crossing`). This is the contradiction.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

namespace PlaneEmbedding

variable (φ : PlaneEmbedding G R)

/-- The image of a path list with at least two vertices is compact and connected. -/
theorem isCompact_isConnected_pathImage {l : List V} (h : IsPathList G R l) (h2 : 2 ≤ l.length) :
    IsCompact (φ.pathImage l) ∧ IsConnected (φ.pathImage l) := by
  obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
    cases l with
    | nil => simp at h2
    | cons x l' => exact ⟨x, l', rfl⟩
  have hl' : l' ≠ [] := by rintro rfl; simp at h2
  have hL := φ.isLine_pathImage hl' h
  obtain ⟨a, ha, hra, -, -⟩ := hL.exists_arc
  refine ⟨hL.isCompact, ?_⟩
  rw [← hra]
  exact isConnected_range ha.1

/-- The images of two paths of `G` on `R` with disjoint supports are disjoint. -/
theorem disjoint_pathImage {l₁ l₂ : List V} (h₁ : IsPathList G R l₁) (h₂ : IsPathList G R l₂)
    (hd : l₁.Disjoint l₂) : Disjoint (φ.pathImage l₁) (φ.pathImage l₂) := by
  rw [Set.disjoint_iff]
  refine (φ.pathImage_inter_pathImage h₁ h₂ fun p hp q hq he => ?_).trans ?_
  · have hp1 : p.1 ∈ l₁ := (List.of_mem_zip hp).1
    have hp2 : p.2 ∈ l₁ := List.mem_of_mem_tail (List.of_mem_zip hp).2
    have hq1 : q.1 ∈ l₂ := (List.of_mem_zip hq).1
    have hq2 : q.2 ∈ l₂ := List.mem_of_mem_tail (List.of_mem_zip hq).2
    rcases Sym2.eq_iff.mp he with ⟨h, -⟩ | ⟨h, -⟩
    · exact hd hp1 (h ▸ hq1)
    · exact hd hp1 (h ▸ hq2)
  · rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact hd hy1 hy2

end PlaneEmbedding

/-- The ends of two crossing paths alternate on the image `F` of the frame: removing the points of
`C[i]` and `C[j]` from `F` leaves the points of `C[r]` and `C[s]` in different components, when
`i < r < j < s`. -/
theorem PlaneEmbedding.pairsCrossOn_cycleImage (φ : PlaneEmbedding G R) {C : List V}
    (hC : IsCycleList G C) (hR : ∀ x ∈ C, x ∈ R) {i r j s : ℕ} (hir : i < r) (hrj : r < j)
    (hjs : j < s) (hs : s < C.length) :
    PairsCrossOn (φ.cycleImage C) (φ.pt C[i]) (φ.pt C[j]) (φ.pt C[r]) (φ.pt C[s]) := by
  set n := C.length with hn
  set C' := C.rotate i with hC'
  have hC'c : IsCycleList G C' := hC.rotate i
  have hR' : ∀ x ∈ C', x ∈ R := fun x hx => hR x (List.mem_rotate.mp hx)
  have hlen : C'.length = n := List.length_rotate _ _
  have hne : C' ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hget : ∀ m (hm : m + i < n), C'[m]'(by omega) = C[m + i] := by
    intro m hm
    rw [List.getElem_rotate]
    congr 1
    exact Nat.mod_eq_of_lt hm
  have hhead : C'.head hne = C[i] := by
    rw [List.head_eq_getElem, hget 0 (by omega)]
    simp
  obtain ⟨hP1, hP2, hF, hI⟩ := φ.cycleImage_split hC'c hR' hne (k := j - i) (by omega) (by omega)
  rw [φ.cycleImage_rotate] at hF
  set L := C' ++ [C'.head hne] with hL
  have hLlen : L.length = n + 1 := by simp [L, hlen]
  have hLget : ∀ m (hm : m + i < n), L[m]'(by omega) = C[m + i] := by
    intro m hm
    rw [List.getElem_append_left (by omega)]
    exact hget m hm
  set A₁ := φ.pathImage (L.take (j - i + 1))
  set A₂ := φ.pathImage (L.drop (j - i))
  have hCk : C'[j - i]'(by omega) = C[j] := by rw [hget _ (by omega)]; congr 1; omega
  rw [hhead, hCk] at hI
  have hnd := hC.2.1
  have hptne : ∀ {a b : ℕ} (ha : a < n) (hb : b < n), a ≠ b → φ.pt C[a] ≠ φ.pt C[b] := by
    intro a b ha hb hab he
    exact hab ((List.Nodup.getElem_inj_iff hnd).mp
      (φ.injOn (hR _ (List.getElem_mem _)) (hR _ (List.getElem_mem _)) he))
  -- `C[r]` is on the first arc and `C[s]` on the second
  have hr1 : φ.pt C[r] ∈ A₁ := by
    refine φ.pt_mem_pathImage hP1 (by rw [List.length_take]; omega) ?_
    rw [show C[r] = L[r - i]'(by omega) by rw [hLget _ (by omega)]; congr 1; omega]
    exact List.mem_iff_getElem.mpr ⟨r - i, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
  have hs2 : φ.pt C[s] ∈ A₂ := by
    refine φ.pt_mem_pathImage hP2 (by rw [List.length_drop]; omega) ?_
    rw [show C[s] = L[s - i]'(by omega) by rw [hLget _ (by omega)]; congr 1; omega]
    exact List.mem_iff_getElem.mpr ⟨s - j, by rw [List.length_drop]; omega,
      by rw [List.getElem_drop]; congr 1; omega⟩
  have hr2 : φ.pt C[r] ∉ A₂ := by
    intro h
    have : φ.pt C[r] ∈ A₁ ∩ A₂ := ⟨hr1, h⟩
    rw [hI] at this
    rcases this with h | h
    · exact hptne (by omega) (by omega) (by omega) h
    · exact hptne (by omega) (by omega) (by omega) h
  have hs1 : φ.pt C[s] ∉ A₁ := by
    intro h
    have : φ.pt C[s] ∈ A₁ ∩ A₂ := ⟨h, hs2⟩
    rw [hI] at this
    rcases this with h | h
    · exact hptne (by omega) (by omega) (by omega) h
    · exact hptne (by omega) (by omega) (by omega) h
  have hcl₁ : IsClosed A₁ := (φ.isCompact_isConnected_pathImage hP1 (by simp; omega)).1.isClosed
  have hcl₂ : IsClosed A₂ := (φ.isCompact_isConnected_pathImage hP2 (by simp; omega)).1.isClosed
  refine ⟨?_, ?_, ?_, ?_, hptne (by omega) (by omega) (by omega), hptne (by omega) (by omega) (by omega),
    hptne (by omega) (by omega) (by omega), hptne (by omega) (by omega) (by omega),
    hptne (by omega) (by omega) (by omega), hptne (by omega) (by omega) (by omega), ?_⟩
  · have : φ.pt C[i] ∈ A₁ ∩ A₂ := by rw [hI]; exact Or.inl rfl
    rw [hF]; exact Or.inl this.1
  · rw [hF]; exact Or.inl hr1
  · have : φ.pt C[j] ∈ A₁ ∩ A₂ := by rw [hI]; exact Or.inr rfl
    rw [hF]; exact Or.inl this.1
  · rw [hF]; exact Or.inr hs2
  · -- the component of `C[r]` stays in the first arc, which misses `C[s]`
    intro he
    have hsub : connectedComponentIn (φ.cycleImage C \ {φ.pt C[i], φ.pt C[j]}) (φ.pt C[r]) ⊆
        A₁ \ {φ.pt C[i], φ.pt C[j]} ∨
        connectedComponentIn (φ.cycleImage C \ {φ.pt C[i], φ.pt C[j]}) (φ.pt C[r]) ⊆
        A₂ \ {φ.pt C[i], φ.pt C[j]} := by
      refine isPreconnected_connectedComponentIn.subset_or_of_separated ?_ ?_ ?_
      · refine (connectedComponentIn_subset _ _).trans ?_
        rw [hF, union_sdiff_distrib]
      · refine disjoint_left.mpr fun z hz hz2 => hz2.2 ?_
        have hz1 : z ∈ A₁ := (closure_minimal sdiff_subset hcl₁) hz
        rw [← hI]
        exact ⟨hz1, hz2.1⟩
      · refine disjoint_left.mpr fun z hz1 hz => hz1.2 ?_
        have hz2 : z ∈ A₂ := (closure_minimal sdiff_subset hcl₂) hz
        rw [← hI]
        exact ⟨hz1.1, hz2⟩
    have hrmem : φ.pt C[r] ∈ φ.cycleImage C \ {φ.pt C[i], φ.pt C[j]} := by
      refine ⟨by rw [hF]; exact Or.inl hr1, ?_⟩
      rintro (h | h)
      · exact hptne (by omega) (by omega) (by omega) h
      · exact hptne (by omega) (by omega) (by omega) h
    have hsmem : φ.pt C[s] ∈ φ.cycleImage C \ {φ.pt C[i], φ.pt C[j]} := by
      refine ⟨by rw [hF]; exact Or.inr hs2, ?_⟩
      rintro (h | h)
      · exact hptne (by omega) (by omega) (by omega) h
      · exact hptne (by omega) (by omega) (by omega) h
    rcases hsub with hsub | hsub
    · exact hs1 (hsub (he ▸ mem_connectedComponentIn hsmem)).1
    · exact hr2 (hsub (mem_connectedComponentIn hrmem)).1

/-- **Proposition 3.2**: "Frames of webs are crossless." -/
theorem IsWebOn.not_isCrossed {S : Set V} {C : List V} (h : IsWebOn G S C) : ¬ IsCrossed G C := by
  classical
  obtain ⟨R, tri, W⟩ := h.exists_webData
  obtain ⟨hC, hCR, φ, hφ⟩ := W.rib
  rintro ⟨a, b, c, d, Q, P, ⟨i, r, j, s, hir, hrj, hjs, hCi, hCr, hCj, hCs⟩, hQ, hP, hdisj⟩
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hCi
  obtain ⟨hr, rfl⟩ := List.getElem?_eq_some_iff.mp hCr
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hCj
  obtain ⟨hs, rfl⟩ := List.getElem?_eq_some_iff.mp hCs
  have hmem : ∀ m (hm : m < C.length), C[m] ∈ R := fun m hm => hCR _ (List.getElem_mem _)
  -- Step 1: the two paths in the rib
  obtain ⟨Q₀, hQ₀, hQ₀R⟩ := W.exists_rib_path Q (hmem i hi) (hmem j hj)
  obtain ⟨P₀, hP₀, hP₀R⟩ := W.exists_rib_path P (hmem r hr) (hmem s hs)
  have hP1 := PlaneEmbedding.isPathList_support hQ₀ fun x hx => (hQ₀R x hx).1
  have hP2 := PlaneEmbedding.isPathList_support hP₀ fun x hx => (hP₀R x hx).1
  have hnd := hC.2.1
  have hne : ∀ {m m' : ℕ} (hm : m < C.length) (hm' : m' < C.length), m ≠ m' → C[m] ≠ C[m'] :=
    fun hm hm' h he => h ((List.Nodup.getElem_inj_iff hnd).mp he)
  have hlen : ∀ {u v : V} (q : G.Walk u v), u ≠ v → 2 ≤ q.support.length := by
    intro u v q huv
    cases q with
    | nil => exact absurd rfl huv
    | cons _ q =>
      rw [Walk.support_cons, List.length_cons]
      exact Nat.succ_le_succ (List.length_pos_of_mem (Walk.start_mem_support q))
  have hl1 := hlen Q₀ (hne hi hj (by omega))
  have hl2 := hlen P₀ (hne hr hs (by omega))
  obtain ⟨hA1, hA2⟩ := φ.isCompact_isConnected_pathImage hP1 hl1
  obtain ⟨hB1, hB2⟩ := φ.isCompact_isConnected_pathImage hP2 hl2
  -- Step 2: the drawing lies in the closed disc bounded by the frame
  have J := isJordanParts (φ.isOArc_cycleImage hC hCR).some
  obtain ⟨hD, hDb⟩ := isClosedDisc_closedInner (φ.isOArc_cycleImage hC hCR)
  have hUD : φ.U ⊆ closedInner (φ.cycleImage C) := by
    intro z hz
    by_cases hzF : z ∈ φ.cycleImage C
    · exact Or.inr hzF
    · have : z ∈ Surface.inner (φ.cycleImage C) ∪ outer (φ.cycleImage C) := by rw [J.union_eq]; exact hzF
      rcases this with h | h
      · exact Or.inl h
      · exact absurd h (disjoint_left.mp (hφ.disjoint_outer hC hCR) hz)
  -- Step 3: disjoint images whose ends alternate on the frame
  have hdisj' : Disjoint (φ.pathImage Q₀.support) (φ.pathImage P₀.support) := by
    refine φ.disjoint_pathImage hP1 hP2 fun x hx1 hx2 => ?_
    exact List.disjoint_left.mp hdisj (hQ₀R x hx1).2 (hP₀R x hx2).2
  have hcross := φ.pairsCrossOn_cycleImage hC hCR hir hrj hjs hs
  rw [← hDb] at hcross
  -- Step 4: the crossing lemma for a closed disc
  have := disc_crossing.{0} (closedInner (φ.cycleImage C)) (φ.pathImage Q₀.support)
    (φ.pathImage P₀.support) _ _ _ _ hD ((φ.pathImage_subset_U hP1).trans hUD)
    ((φ.pathImage_subset_U hP2).trans hUD) hA1 hB1 hA2 hB2
    (φ.pt_mem_pathImage hP1 hl1 (Walk.start_mem_support Q₀))
    (φ.pt_mem_pathImage hP1 hl1 (Walk.end_mem_support Q₀))
    (φ.pt_mem_pathImage hP2 hl2 (Walk.start_mem_support P₀))
    (φ.pt_mem_pathImage hP2 hl2 (Walk.end_mem_support P₀)) hcross
  exact not_disjoint_iff_nonempty_inter.mpr this hdisj'

/-- **Proposition 3.2** for a web on all vertices. -/
theorem IsWeb.not_isCrossed {C : List V} (h : IsWeb G C) : ¬ IsCrossed G C :=
  IsWebOn.not_isCrossed h

end GraphMinor.HP25
