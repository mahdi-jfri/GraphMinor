module

public import GraphMinor.GM08.Section9
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section9Paths
import GraphMinor.GM08.Section8Sleeve
import GraphMinor.GM11.Walks

/-!
# Paths between the normal rings in VIII (9.3)

A path from inside a closed disc to outside it meets its boundary.
For a normal boundary the intersection is a path vertex. Choosing these
vertices on two nested normal rings and shortening within each original
path preserves vertex disjointness. This supplies the path conditions
needed to apply Graph Minors VII (9.4).
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- A path crossing a normal disc boundary has a vertex on it.
This is the path-separation step in VIII (9.3), page 270. -/
theorem exists_path_vertex_on_normal_disc {S : Type u} [TopologicalSpace S] [T2Space S]
    {D P : Drawing S} {Δ B : Set S} (hΔ : IsClosedDisc Δ)
    (hB : IsClosedDisc B) (hBΔ : B ⊆ Δ) (hDU : D.U ⊆ Δ)
    (hn : D.IsNormal (discBd B)) (hPD : P.IsSubdrawing D)
    {a b : S} (hp : P.IsPathBetween a b) (ha : a ∈ B) (hb : b ∉ discInt B) :
    ∃ x ∈ P.V, x ∈ discBd B := by
  have haU : a ∈ P.U := P.V_subset_U (by
    obtain ⟨W, -, hV, -⟩ := hp
    rw [hV]
    exact W.start_mem_support)
  have hbU : b ∈ P.U := P.V_subset_U (by
    obtain ⟨W, -, hV, -⟩ := hp
    rw [hV]
    exact W.end_mem_support)
  have hmeet : (P.U ∩ discBd B).Nonempty := by
    by_contra hnone
    have hd := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnone)
    rcases side_of_closedDisc hΔ hBΔ (hPD.U_subset.trans hDU) hB
        (isPreconnected_U_of_isPathBetween hp) hd with hin | hout
    · exact hb (hin hbU)
    · exact disjoint_left.mp hout haU ha
  obtain ⟨x, hxP, hxB⟩ := hmeet
  exact ⟨x, mem_subdrawing_vertex_of_mem_U hPD hxP
    (hn ⟨hxB, hPD.U_subset hxP⟩), hxB⟩

/-- Disjoint paths from an inner disc to outside an outer disc yield
as many disjoint paths between their normal boundaries. Shortening each
path within its own drawing preserves disjointness. -/
theorem hasDisjointPathsBetween_normal_discs {S : Type u} [TopologicalSpace S] [T2Space S]
    {D : Drawing S} {Δ B₁ B₂ : Set S} (hΔ : IsClosedDisc Δ)
    (hB₁ : IsClosedDisc B₁) (hB₂ : IsClosedDisc B₂)
    (hB₁₂ : B₁ ⊆ B₂) (hB₂Δ : B₂ ⊆ Δ) (hDU : D.U ⊆ Δ)
    (hn₁ : D.IsNormal (discBd B₁)) (hn₂ : D.IsNormal (discBd B₂))
    {n : ℕ} (P : Fin n → Drawing S) (a b : Fin n → S)
    (hP : ∀ i, (P i).IsSubdrawing D ∧ (P i).IsPathBetween (a i) (b i) ∧
      a i ∈ B₁ ∧ b i ∉ discInt B₂)
    (hdis : Pairwise fun i j => Disjoint (P i).V (P j).V) :
    GM07.HasDisjointPathsBetween D (discBd B₁) (discBd B₂) n := by
  classical
  have hx : ∀ i, ∃ x ∈ (P i).V, x ∈ discBd B₁ := fun i =>
    exists_path_vertex_on_normal_disc hΔ hB₁ (hB₁₂.trans hB₂Δ) hDU hn₁
      (hP i).1 (hP i).2.1 (hP i).2.2.1
      (fun hb => (hP i).2.2.2 (discInt_mono_of_closedDisc hΔ
        (hB₁₂.trans hB₂Δ) hB₁ hB₁₂ hB₂Δ hB₂ hb))
  have hy : ∀ i, ∃ y ∈ (P i).V, y ∈ discBd B₂ := fun i =>
    exists_path_vertex_on_normal_disc hΔ hB₂ hB₂Δ hDU hn₂
      (hP i).1 (hP i).2.1 (hB₁₂ (hP i).2.2.1)
      (hP i).2.2.2
  choose x hxV hxB using hx
  choose y hyV hyB using hy
  have hQ : ∀ i, ∃ Q : Drawing S, Q.IsSubdrawing (P i) ∧ Q.IsPathBetween (x i) (y i) := by
    intro i
    obtain ⟨W, -⟩ := exists_walk_supported_by_preconnected (P i)
      (isPreconnected_U_of_isPathBetween (hP i).2.1) (Subset.refl _)
      (hxV i) ((P i).V_subset_U (hxV i)) (hyV i) ((P i).V_subset_U (hyV i))
    obtain ⟨W', hs, -, -⟩ := GM09.exists_isSimple_subwalk W
    exact ⟨GM11.walkDrawing (P i) W', GM11.walkDrawing_isSubdrawing _ _,
      GM11.walkDrawing_isPathBetween _ hs⟩
  choose Q hQP hQpath using hQ
  refine ⟨Q, x, y, fun i => ⟨(hQP i).trans (hP i).1, hxB i, hyB i, hQpath i⟩, ?_⟩
  intro i j hij
  exact (hdis hij).mono (hQP i).1 (hQP j).1

end GraphMinor.GM08
