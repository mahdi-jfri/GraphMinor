module

public import GraphMinor.HP25.Link
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.HP25.Prop23
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Ribs are connected

Humeau and Pous, proof of Lemma 3.3 (page 9): "Observe that ribs are connected". The paper gives no
proof. We prove the form that the proofs use: a nonempty set `K` of vertices of a rib that contains
all the neighbours of its vertices meets the frame (`IsRibEmbedding.meets_frame`). So every vertex
of a rib is joined to the frame by a path of the rib (`IsRibEmbedding.reach_frame`).

The argument. Suppose `K` misses the frame. Let `A` be the union of the closed triangles with
vertices in `K`. The set `A` is closed. It is also open:
* a point of an open triangle has the face of the triangle around it;
* a point of the line of an edge `uw` with `u ∈ K`, other than its ends, has a small disc around it
  that lies on the line or in the two faces at `uw`, and these faces are triangles of `A` since `uw`
  is not on the frame;
* the point of a vertex `v ∈ K` has a small disc around it whose points lie on lines at `v` or in
  faces whose frontier passes through a line at `v` or through the point of `v`; such a face is a
  triangle with vertex `v`, and so it is a triangle of `A`.
Since the plane is connected, `A` is the whole plane. But the triangles miss the outer domain of the
frame. This is a contradiction.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface Metric

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

namespace PlaneEmbedding

variable {φ : PlaneEmbedding G R} {C : List V}

/-- A vertex whose point lies on the image of a cycle of `G` on `R` is a vertex of the cycle. -/
theorem mem_of_pt_mem_cycleImage {L : List V} (hL : IsCycleList G L) (hLR : ∀ y ∈ L, y ∈ R)
    {w : V} (hw : w ∈ R) (h : φ.pt w ∈ φ.cycleImage L) : w ∈ L := by
  simp only [cycleImage, mem_iUnion] at h
  obtain ⟨q, hq, h⟩ := h
  have h1 := List.of_mem_zip hq
  rcases φ.avoid _ (hLR _ h1.1) _ (hLR _ (List.mem_rotate.mp h1.2)) (hL.2.2 q hq) w hw h with
    rfl | rfl
  · exact h1.1
  · exact List.mem_rotate.mp h1.2

/-- **Every set of rib vertices closed under neighbours meets the frame.** -/
theorem IsRibEmbedding.meets_frame (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {K : Set V} (hKR : K ⊆ R) (hKne : K.Nonempty)
    (hKcl : ∀ v ∈ K, ∀ w ∈ R, G.Adj v w → w ∈ K) : ∃ v ∈ K, v ∈ C := by
  classical
  by_contra hno
  push Not at hno
  have hKfin : K.Finite := φ.finite.subset hKR
  -- the closed triangles with vertices in `K`
  set A : Set ℂ := ⋃ a ∈ K, ⋃ b ∈ K, ⋃ c ∈ K, ⋃ (_ : G.Adj a b ∧ G.Adj b c ∧ G.Adj a c),
    closure (Surface.inner (φ.cycleImage [a, b, c])) with hA
  have hAc : IsClosed A := hKfin.isClosed_biUnion fun a _ => hKfin.isClosed_biUnion fun b _ =>
    hKfin.isClosed_biUnion fun c _ => isClosed_iUnion_of_finite fun _ => isClosed_closure
  have htri : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, G.Adj a b → G.Adj b c → G.Adj a c →
      IsTriangleOn G R a b c := fun a ha b hb c hc hab hbc hac =>
    ⟨hKR ha, hKR hb, hKR hc, hab, hbc, hac⟩
  have hJT : ∀ {a b c}, IsTriangleOn G R a b c → IsJordanParts (φ.cycleImage [a, b, c]) :=
    fun hT => isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some
  have hmemA : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, ∀ (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c),
      closure (Surface.inner (φ.cycleImage [a, b, c])) ⊆ A := by
    intro a ha b hb c hc hab hbc hac p hp
    simp only [hA, mem_iUnion]
    exact ⟨a, ha, b, hb, c, hc, ⟨hab, hbc, hac⟩, hp⟩
  have hnC : ∀ u ∈ K, ∀ w, ¬ IsCycleEdge C u w := fun u hu w h => hno u hu h.mem_left
  -- the line of an edge at `K` lies in `A`
  have hlineA : ∀ u ∈ K, ∀ w ∈ R, G.Adj u w → φ.line u w ⊆ A := by
    intro u hu w hw huw
    have hwK := hKcl u hu w hw huw
    obtain ⟨z, -, -, hz, -⟩ := (hφ.common_neighbours hC hR (hKR hu) hw huw).2.2 (hnC u hu w)
    have hzK := hKcl u hu z hz.1 hz.2.1
    have hT := htri u hu w hwK z hzK huw hz.2.2 hz.2.1
    intro p hp
    refine hmemA u hu w hwK z hzK huw hz.2.2 hz.2.1 (frontier_subset_closure ?_)
    rw [(hJT hT).frontier_inner, φ.cycleImage_three]
    exact Or.inl (Or.inl hp)
  -- a face whose closure meets the line of an edge at `K` away from its ends lies in `A`
  have hfaceA : ∀ u ∈ K, ∀ w ∈ R, G.Adj u w → ∀ f ∈ φ.faces, ∀ p ∈ φ.line u w, p ≠ φ.pt u →
      p ≠ φ.pt w → p ∈ closure f → f ⊆ A := by
    intro u hu w hw huw f hf p hp h1 h2 hpf
    obtain ⟨z, hz, huz, hwz, rfl⟩ := hφ.face_at_inner_edge hC hR (hKR hu) hw huw (hnC u hu w) hf
      hp h1 h2 hpf
    have hwK := hKcl u hu w hw huw
    exact subset_closure.trans (hmemA u hu w hwK z (hKcl u hu z hz huz) huw hwz huz)
  -- a point of `U` near which a face lies: the frontier of the face meets the disc
  have hmeetU : ∀ (W : Set ℂ), IsPreconnected W → ∀ f ∈ φ.faces, (W ∩ f).Nonempty →
      (W \ f).Nonempty → ∃ p' ∈ W, p' ∈ closure f ∧ p' ∉ f ∧ p' ∈ φ.U := by
    intro W hW f hf ⟨q, hqW, hqf⟩ ⟨p, hpW, hpf⟩
    have hfo := φ.isOpen_of_mem_faces hf
    obtain ⟨p', hp'W, hp'c, hp'f⟩ : ∃ p' ∈ W, p' ∈ closure f ∧ p' ∉ f := by
      by_contra hno'
      push Not at hno'
      have hsub := hW.subset_left_of_subset_union hfo.1 isClosed_closure.isOpen_compl
        (disjoint_compl_right_iff_subset.mpr subset_closure)
        (fun z hz => by
          by_cases h : z ∈ closure f
          · exact Or.inl (hno' z hz h)
          · exact Or.inr h) ⟨q, hqW, hqf⟩
      exact hpf (hsub hpW)
    refine ⟨p', hp'W, hp'c, hp'f, ?_⟩
    by_contra hp'U
    obtain ⟨hf', hp'f'⟩ := φ.mem_faces_of_notMem hp'U
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hp'c _ (φ.isOpen_of_mem_faces hf').1 hp'f'
    exact hp'f (φ.eq_of_mem_faces hf' hf hz1 hz2 ▸ hp'f')
  -- a point of a line at `K`, other than its ends, is an interior point of `A`
  have hlineInt : ∀ u ∈ K, ∀ w ∈ R, G.Adj u w → ∀ p ∈ φ.line u w, p ≠ φ.pt u → p ≠ φ.pt w →
      p ∈ interior A := by
    intro u hu w hw huw p hp h1 h2
    have hprest : p ∉ φ.rest u w := fun h => by
      rcases φ.line_inter_rest (hKR hu) hw huw ⟨hp, h⟩ with h | h
      · exact h1 h
      · exact h2 h
    obtain ⟨δ, hδ, hδr⟩ := Metric.isOpen_iff.mp (φ.isClosed_rest u w).isOpen_compl _ hprest
    refine mem_interior.mpr ⟨ball p δ, fun q hq => ?_, isOpen_ball, mem_ball_self hδ⟩
    have hUeq := φ.U_eq_rest (hKR hu) hw huw
    by_cases hqU : q ∈ φ.U
    · rw [hUeq] at hqU
      rcases hqU with h | h
      · exact absurd h (hδr hq)
      · exact hlineA u hu w hw huw h
    · obtain ⟨hf, hqf⟩ := φ.mem_faces_of_notMem hqU
      have hpU : p ∈ φ.U := φ.line_subset_U (hKR hu) hw huw hp
      obtain ⟨p', hp'B, hp'c, -, hp'U⟩ := hmeetU _ isPreconnected_ball _ hf ⟨q, hq, hqf⟩
        ⟨p, mem_ball_self hδ, fun h => (φ.isOpen_of_mem_faces hf).2.2 h hpU⟩
      rw [hUeq] at hp'U
      rcases hp'U with h | hp'L
      · exact absurd h (hδr hp'B)
      · have h1' : p' ≠ φ.pt u := fun h => hδr hp'B (h ▸ Or.inl ⟨u, hKR hu, rfl⟩)
        have h2' : p' ≠ φ.pt w := fun h => hδr hp'B (h ▸ Or.inl ⟨w, hw, rfl⟩)
        exact hfaceA u hu w hw huw _ hf p' hp'L h1' h2' hp'c hqf
  -- the point of a vertex of `K` is an interior point of `A`
  have hptInt : ∀ v ∈ K, φ.pt v ∈ interior A := by
    intro v hv
    set Z : Set ℂ := φ.pt '' (R \ {v}) ∪
      ⋃ u ∈ R, ⋃ w ∈ R, ⋃ (_ : G.Adj u w ∧ u ≠ v ∧ w ≠ v), φ.line u w with hZ
    have hZc : IsClosed Z := (((φ.finite.subset sdiff_subset).image _).isCompact.union
      (φ.finite.isCompact_biUnion fun u hu => φ.finite.isCompact_biUnion fun w hw =>
        isCompact_iUnion fun h => (φ.isLine u hu w hw h.1).isCompact)).isClosed
    have hvZ : φ.pt v ∉ Z := by
      rintro (⟨w, ⟨hw, hwv⟩, he⟩ | h)
      · exact hwv (φ.injOn hw (hKR hv) he)
      · simp only [mem_iUnion] at h
        obtain ⟨u, hu, w, hw, ⟨huw, huv, hwv⟩, h⟩ := h
        rcases φ.avoid u hu w hw huw v (hKR hv) h with h | h
        · exact huv h.symm
        · exact hwv h.symm
    obtain ⟨ε, hε, hεZ⟩ := Metric.isOpen_iff.mp hZc.isOpen_compl _ hvZ
    have hptZ : ∀ w ∈ R, w ≠ v → φ.pt w ∈ Z := fun w hw hwv => Or.inl ⟨w, ⟨hw, hwv⟩, rfl⟩
    -- a drawn point near `v` other than `v` lies on a line at `v`
    have hUB : ∀ p ∈ φ.U, p ∈ ball (φ.pt v) ε → p ≠ φ.pt v →
        ∃ w, w ∈ R ∧ G.Adj v w ∧ p ∈ φ.line v w := by
      intro p hpU hpB hpv
      rcases hpU with ⟨w, hw, rfl⟩ | hpU
      · by_cases hwv : w = v
        · exact absurd (congrArg φ.pt hwv) hpv
        · exact absurd (hptZ w hw hwv) (hεZ hpB)
      · simp only [mem_iUnion] at hpU
        obtain ⟨u, hu, w, hw, huw, hp⟩ := hpU
        by_cases huv : u = v
        · subst huv; exact ⟨w, hw, huw, hp⟩
        · by_cases hwv : w = v
          · subst hwv; exact ⟨u, hu, huw.symm, by rwa [φ.line_comm]⟩
          · refine absurd ?_ (hεZ hpB)
            right
            simp only [mem_iUnion]
            exact ⟨u, hu, w, hw, ⟨huw, huv, hwv⟩, hp⟩
    refine mem_interior.mpr ⟨ball (φ.pt v) ε, fun q hq => ?_, isOpen_ball, mem_ball_self hε⟩
    by_cases hqv : q = φ.pt v
    · obtain ⟨w, hw, hvw⟩ := hφ.exists_adj hC hR (hKR hv)
      exact hqv ▸ hlineA v hv w hw hvw (φ.isLine v (hKR hv) w hw hvw).left_mem
    by_cases hqU : q ∈ φ.U
    · obtain ⟨w, hw, hvw, hqL⟩ := hUB q hqU hq hqv
      exact hlineA v hv w hw hvw hqL
    obtain ⟨hf, hqf⟩ := φ.mem_faces_of_notMem hqU
    set f := connectedComponentIn (univ \ φ.U) q
    have hfo := φ.isOpen_of_mem_faces hf
    have hvU : φ.pt v ∈ φ.U := φ.pt_mem_U (hKR hv)
    obtain ⟨p', hp'B, hp'c, hp'f, hp'U⟩ := hmeetU _ isPreconnected_ball _ hf ⟨q, hq, hqf⟩
      ⟨φ.pt v, mem_ball_self hε, fun h => hfo.2.2 h hvU⟩
    by_cases hp'v : p' = φ.pt v
    · -- the point of `v` is on the frontier of the face `f`
      have hfr : φ.pt v ∈ frontier f := by
        rw [frontier, hfo.1.interior_eq]
        exact ⟨hp'v ▸ hp'c, fun h => hfo.2.2 h hvU⟩
      have JF := isJordanParts (φ.isOArc_cycleImage hC hR).some
      rcases hφ.face_cases hC hR hf with he | ⟨a, b, c, hT, he⟩
      · rw [he, JF.frontier_outer] at hfr
        exact (hno v hv (mem_of_pt_mem_cycleImage hC hR (hKR hv) hfr)).elim
      · have hJ := hJT hT
        rw [he, hJ.frontier_inner] at hfr
        have hvT := mem_of_pt_mem_cycleImage hT.isCycleList hT.mem (hKR hv) hfr
        obtain ⟨ha, hb, hc, hab, hbc, hac⟩ := hT
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hvT
        have hK3 : a ∈ K ∧ b ∈ K ∧ c ∈ K := by
          rcases hvT with rfl | rfl | rfl
          · exact ⟨hv, hKcl _ hv _ hb hab, hKcl _ hv _ hc hac⟩
          · exact ⟨hKcl _ hv _ ha hab.symm, hv, hKcl _ hv _ hc hbc⟩
          · exact ⟨hKcl _ hv _ ha hac.symm, hKcl _ hv _ hb hbc.symm, hv⟩
        rw [he] at hqf
        exact hmemA a hK3.1 b hK3.2.1 c hK3.2.2 hab hbc hac (subset_closure hqf)
    · obtain ⟨w, hw, hvw, hp'L⟩ := hUB p' hp'U hp'B hp'v
      have h2 : p' ≠ φ.pt w := by
        rintro rfl
        exact hεZ hp'B (hptZ w hw hvw.ne.symm)
      exact hfaceA v hv w hw hvw f hf p' hp'L hp'v h2 hp'c hqf
  -- `A` is open
  have hAo : IsOpen A := by
    refine isOpen_iff_forall_mem_open.mpr fun p hp => ⟨interior A, interior_subset, isOpen_interior, ?_⟩
    simp only [hA, mem_iUnion] at hp
    obtain ⟨a, ha, b, hb, c, hc, ⟨hab, hbc, hac⟩, hpc⟩ := hp
    have hT := htri a ha b hb c hc hab hbc hac
    have hJ := hJT hT
    rw [closure_eq_self_union_frontier, hJ.frontier_inner] at hpc
    rcases hpc with hpi | hpT
    · exact mem_interior.mpr ⟨_, subset_closure.trans (hmemA a ha b hb c hc hab hbc hac), hJ.isOpen_inner,
        hpi⟩
    -- a point of a line of the triangle
    have hline : ∀ u ∈ K, ∀ w ∈ K, G.Adj u w → p ∈ φ.line u w → p ∈ interior A := by
      intro u hu w hw huw hpL
      by_cases h1 : p = φ.pt u
      · exact h1 ▸ hptInt u hu
      by_cases h2 : p = φ.pt w
      · exact h2 ▸ hptInt w hw
      exact hlineInt u hu w (hKR hw) huw p hpL h1 h2
    rw [φ.cycleImage_three] at hpT
    rcases hpT with (h | h) | h
    · exact hline a ha b hb hab h
    · exact hline b hb c hc hbc h
    · exact hline c hc a ha hac.symm h
  -- `A` is the whole plane, but it misses the outer domain of the frame
  obtain ⟨v, hv⟩ := hKne
  have hAne : A.Nonempty := ⟨φ.pt v, interior_subset (hptInt v hv)⟩
  have hAu : A = univ := IsClopen.eq_univ ⟨hAc, hAo⟩ hAne
  have JF := isJordanParts (φ.isOArc_cycleImage hC hR).some
  have hout := hφ.outer_mem_faces hC hR
  obtain ⟨o, ho⟩ : (outer (φ.cycleImage C)).Nonempty := JF.isConnected_outer.nonempty
  have hoA : o ∈ A := hAu ▸ mem_univ o
  simp only [hA, mem_iUnion] at hoA
  obtain ⟨a, ha, b, hb, c, hc, ⟨hab, hbc, hac⟩, hoc⟩ := hoA
  have hT := htri a ha b hb c hc hab hbc hac
  have hJ := hJT hT
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hoc _ JF.isOpen_outer ho
  have he := φ.eq_of_mem_faces hout (hφ.inner_mem_faces hT).1 hz1 hz2
  exact JF.not_isBounded_outer (he ▸ hJ.isBounded_inner)

/-- Every vertex of a rib is joined to the frame by a path of the rib. -/
theorem IsRibEmbedding.reach_frame (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {x : V} (hx : x ∈ R) :
    ∃ c ∈ C, (restrict G R).Reachable x c := by
  obtain ⟨c, hcK, hc⟩ := hφ.meets_frame hC hR (K := {v | v ∈ R ∧ (restrict G R).Reachable x v})
    (fun v hv => hv.1) ⟨x, hx, Reachable.refl _⟩
    (fun v hv w hw hvw => ⟨hw, hv.2.trans (Adj.reachable ⟨hvw, hv.1, hw⟩)⟩)
  exact ⟨c, hc, hcK.2⟩

end PlaneEmbedding

end GraphMinor.HP25
