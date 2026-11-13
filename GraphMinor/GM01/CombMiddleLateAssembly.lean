module

public import GraphMinor.GM01.CombMiddleAttachmentPaths
public import GraphMinor.GM01.CombJoinPieces
import GraphMinor.GM01.DisjointCleanHitJoins

/-!
# Joining the middle and late pieces while retaining a clean root path

For Graph Minors I, (4.14), page 59, join the middle of the layer
subdivision to the old late piece along the second attachment.
The first attachment and its internal path remain disjoint from
this join and meet the new comb only at its root. Their vertex bounds
also keep the old early piece available for the last join.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

private theorem disjoint_of_clean_hit {α : Type*} {A X S : Set α} {a : α}
    (hAX : A ∩ X = {a}) (hSX : S ⊆ X) (ha : a ∉ S) : Disjoint A S := by
  apply Set.disjoint_left.mpr
  intro x hxA hxS
  have hxa : x = a := mem_singleton_iff.mp (hAX ▸ ⟨hxA, hSX hxS⟩)
  exact ha (hxa ▸ hxS)

/-- The first joined comb and the remaining clean root path in the
contraction for GM01 (4.14), page 59. All vertices of the joined
piece lie in the subdivision, the late piece, or the second path. -/
theorem exists_middle_late_comb_with_clean_root_path {α β : Type*} {γ L b : ℕ}
    (hL : 6 ≤ L) (hb : 0 < b) {G D : Graph α β} (hDG : D ≤ G)
    (c : (pathComb γ L).verts → α) (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hV : V(D) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (B : RootedGraph α β) (hBG : B.graph ≤ G)
    (MB : RootedMinorModel (rootedPathComb γ b hb) B) (hDB : Disjoint V(D) V(B.graph))
    {d₁ d₂ w₁ : α} (hd₁ : d₁ ∈ combFirstEndSupport (by omega) c P)
    (hd₂ : d₂ ∈ combSecondEndSupport (by omega) c P)
    {P₁ P₂ : Graph α β} (hP₁ : IsGraphPathWithEnds G P₁ d₁ w₁)
    (hP₂ : IsGraphPathWithEnds G P₂ d₂ B.root.val)
    (hP₁D : V(P₁) ∩ V(D) = {d₁}) (hP₂D : V(P₂) ∩ V(D) = {d₂})
    (hP₁B : Disjoint V(P₁) V(B.graph)) (hP₂B : V(P₂) ∩ V(B.graph) = {B.root.val})
    (hP₁P₂ : Disjoint V(P₁) V(P₂)) :
    ∃ K : RootedGraph α β, K.graph ≤ G ∧
      V(K.graph) ⊆ V(D) ∪ V(B.graph) ∪ V(P₂) ∧
      HasRootedMinor (rootedPathComb γ ((L - 4) + b) (by omega)) K ∧
      ∃ J : Graph α β, IsGraphPathWithEnds G J w₁ K.root.val ∧
        V(J) ∩ V(K.graph) = {K.root.val} ∧ V(J) ⊆ V(P₁) ∪ V(D) := by
  have hcentres : ∀ v, c v ∈ V(D) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  let A := rootedCombSegment (by omega : 0 < L - 4) D c P 2 (by omega : 2 + (L - 4) ≤ L)
  obtain ⟨hAD, _, MA, hACentres⟩ := combSegment_model (by omega : 0 < L - 4) c hc hcentres P
    hPaths hInter 2 (by omega : 2 + (L - 4) ≤ L)
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hQ₁A, hQ₂A, hQ₁Q₂, hQ₁End₂, hQ₂End₁⟩ :=
    exists_disjoint_paths_from_ends_to_middle hL c hc P hV hPaths hInter hd₁ hd₂
  let z := c ⟨Sum.inl ⟨L - 3, by omega⟩, pathComb_spine_mem γ L _⟩
  have hFirstA := disjoint_combSegmentSupports hc P hRanges (fun e f hne ↦ (hInter e f hne).1)
    0 2 (by omega : 0 + 2 ≤ L) (by omega : 2 + (L - 4) ≤ L) (by omega)
  have hASecond := disjoint_combSegmentSupports hc P hRanges (fun e f hne ↦ (hInter e f hne).1)
    2 (L - 2) (by omega : 2 + (L - 4) ≤ L) (by omega : L - 2 + 2 ≤ L) (by omega)
  have hd₁A : d₁ ∉ V(A.graph) := fun h ↦ Set.disjoint_left.mp hFirstA hd₁ h
  have hd₂A : d₂ ∉ V(A.graph) := fun h ↦ Set.disjoint_left.mp hASecond h hd₂
  have hP₁A := disjoint_of_clean_hit hP₁D hAD.vertexSet_mono hd₁A
  have hP₂A := disjoint_of_clean_hit hP₂D hAD.vertexSet_mono hd₂A
  let J₁ := subgraphUnion G P₁ Q₁
  let J₂ := subgraphUnion G P₂ Q₂
  have hJ₁ : IsGraphPathWithEnds G J₁ w₁ A.root.val := isGraphPath_join_of_clean_hit hDG hP₁ hP₁D hQ₁
  have hJ₂ : IsGraphPathWithEnds G J₂ B.root.val z := isGraphPath_join_of_clean_hit hDG hP₂ hP₂D hQ₂
  have hJ₁J₂ : Disjoint V(J₁) V(J₂) := disjoint_clean_hit_joins hP₁D.subset hP₂D.subset
    hQ₁.le.vertexSet_mono hQ₂.le.vertexSet_mono hP₁P₂ hQ₁Q₂
    (fun h ↦ Set.disjoint_left.mp hQ₂End₁ h hd₁) (fun h ↦ Set.disjoint_left.mp hQ₁End₂ h hd₂)
  have hJ₁B : Disjoint V(J₁) V(B.graph) := hP₁B.union_left (hDB.mono_left hQ₁.le.vertexSet_mono)
  have hQ₂ATyped : V(Q₂) ∩ V(A.graph) = {z} := hQ₂A
  have hQ₁ATyped : V(Q₁) ∩ V(A.graph) = {A.root.val} := hQ₁A
  have hJ₂A : V(J₂) ∩ V(A.graph) = {z} := by
    change (V(P₂) ∪ V(Q₂)) ∩ V(A.graph) = {z}
    rw [Set.union_inter_distrib_right, Set.disjoint_iff_inter_eq_empty.mp hP₂A, hQ₂ATyped, Set.empty_union]
  have hJ₂B : V(J₂) ∩ V(B.graph) = {B.root.val} := by
    change (V(P₂) ∪ V(Q₂)) ∩ V(B.graph) = {B.root.val}
    rw [Set.union_inter_distrib_right, hP₂B,
      Set.disjoint_iff_inter_eq_empty.mp (hDB.mono_left hQ₂.le.vertexSet_mono), Set.union_empty]
  have hJ₁A : V(J₁) ∩ V(A.graph) = {A.root.val} := by
    change (V(P₁) ∪ V(Q₁)) ∩ V(A.graph) = {A.root.val}
    rw [Set.union_inter_distrib_right, Set.disjoint_iff_inter_eq_empty.mp hP₁A, hQ₁ATyped, Set.empty_union]
  have hlast : combShiftEmbedding 2 (by omega : 2 + (L - 4) ≤ L)
      (pathCombLastSpine γ (L - 4) (by omega)) =
      (⟨Sum.inl ⟨L - 3, by omega⟩, pathComb_spine_mem γ L _⟩ : (pathComb γ L).verts) := by
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Fin.ext
    change 2 + (L - 4 - 1) = L - 3
    omega
  have hz : z ∈ MA.branch (pathCombLastSpine γ (L - 4) (by omega)) := by
    have hh := hACentres (pathCombLastSpine γ (L - 4) (by omega))
    rw [hlast] at hh
    exact hh
  obtain ⟨K, hKG, hKV, hroot, hMK⟩ := exists_rooted_comb_join_piece (by omega : 0 < L - 4) hb A B
    (hAD.trans hDG) hBG (hDB.mono_left hAD.vertexSet_mono) MA MB hz hJ₂.symm hJ₂A hJ₂B
  have hKBound : V(K.graph) ⊆ V(D) ∪ V(B.graph) ∪ V(P₂) := by
    rw [hKV]
    intro x hx
    rcases hx with (hxA | hxB) | (hxP | hxQ)
    · exact Or.inl (Or.inl (hAD.vertexSet_mono hxA))
    · exact Or.inl (Or.inr hxB)
    · exact Or.inr hxP
    · exact Or.inl (Or.inl (hQ₂.le.vertexSet_mono hxQ))
  have hMeet : V(J₁) ∩ V(K.graph) = {K.root.val} := by
    rw [hroot]
    rw [hKV, Set.inter_union_distrib_left, Set.inter_union_distrib_left, hJ₁A,
      Set.disjoint_iff_inter_eq_empty.mp hJ₁B, Set.disjoint_iff_inter_eq_empty.mp hJ₁J₂,
      Set.union_empty, Set.union_empty]
  refine ⟨K, hKG, hKBound, hMK, J₁, ?_, hMeet, ?_⟩
  · rw [hroot]
    exact hJ₁
  · exact union_subset subset_union_left (hQ₁.le.vertexSet_mono.trans subset_union_right)

end GraphMinor.GM01
