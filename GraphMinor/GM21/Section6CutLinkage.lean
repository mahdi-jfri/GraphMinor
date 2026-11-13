module

public import GraphMinor.GM21.Section6CutCases
import GraphMinor.GM21.Section6ClaimFourGap
import GraphMinor.GM21.Section6SplitLinkage

/-!
# Graph Minors XXI, (6.3), claim (2): the linkage of the split graph

Claim (2) of the proof of (6.3) (page 28 of the preprint): "But by (2.4), it follows that
$G'$ has an exhaustive vital $(p + 4q)$-linkage". The graph `G'` is `G` split first along
`V(μ(a))` and then along the copies of `V(μ(b))`, each of at most `q` vertices. (2.4), used once
for each split vertex (`isVitalPLinkage_splitAlong`), gives a vital linkage with at most
`p + 2q + 2q` terminals (`isExhaustiveLinkage_cut`). Its terminals are copies of terminals of `L` or
of split vertices, and all of these lie in the graphs of the new supports (`nm2_mem_pieces`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface Hypergraph GraphMinor.GM21.Split

universe u v

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]

omit [TopologicalSpace S] in
theorem eq_of_splitName_eq_inr_inl {X : Set α} {c : Bool} {v w : α}
    (h : splitName X c v = .inr (.inl w)) : v = w := by
  unfold splitName at h
  split_ifs at h <;> simp_all

omit [TopologicalSpace S] in
theorem eq_of_splitName_eq_inr_inr {X : Set α} {c : Bool} {v w : α}
    (h : splitName X c v = .inr (.inr w)) : v = w := by
  unfold splitName at h
  split_ifs at h <;> simp_all

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

/-- **Every copy of a vertex of some `H_j`, or of `μ(a)` or `μ(b)`, is a vertex of the graph of a
new support.** -/
theorem nm2_mem_pieces (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) {a b : S}
    (ha : a ∈ Γ.V ∩ bd S) (hb : b ∈ Γ.V ∩ bd S) (hab : a ≠ b) {cb : Bool} {Apf Bpf : Set S}
    {r₂ : ℕ} {P : Fin r₂ → Set S} {τ : Fin r₂ → Fin r} {col : Fin r₂ → Bool × Bool}
    (hsys : IsPieceSystem G Γ Γ_sub μ F_star a b cb Apf Bpf P τ col) (c : Bool × Bool) {v : α}
    (hv : v ∈ (⋃ j, (H j).vertexSet) ∪
      ((μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet)) :
    nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) c v ∈
      ⋃ i, nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (col i) ''
        (supportGraph G Γ μ (P i)).vertexSet := by
  by_cases hab' : v ∈ (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet
  · by_cases hvΓ : v ∈ Γ_sub.vertexSet
    · rw [← hP.ιV_image] at hvΓ
      obtain ⟨u, hu, rfl⟩ := hvΓ
      rcases hab' with hva | hvb
      · have hua : u = a := (ιV_mem_μ_iff hP ha hu).mp hva
        obtain ⟨i, hai, hci⟩ := hsys.bothA c.1
        refine mem_iUnion.mpr ⟨i, ιV u, mem_supportGraph_of_vertex hP (hsys.sub i)
          ⟨hu, hua ▸ hai⟩ (hua ▸ hva), nm2_eq_of_sides (fun _ => hci) fun hd => ?_⟩
        exact absurd (hua.symm.trans ((splitName_mem_splitB_iff hP ha hb hab cb _ hu).mp hd)) hab
      · have hub : u = b := (ιV_mem_μ_iff hP hb hu).mp hvb
        obtain ⟨i, hbi, hci⟩ := hsys.bothB c.2
        refine mem_iUnion.mpr ⟨i, ιV u, mem_supportGraph_of_vertex hP (hsys.sub i)
          ⟨hu, hub ▸ hbi⟩ (hub ▸ hvb), nm2_eq_of_sides (fun hd => ?_) fun _ => hci⟩
        exact absurd (hub.symm.trans ((ιV_mem_μ_iff hP ha hu).mp hd)) (Ne.symm hab)
    · obtain ⟨i, hi, hc⟩ := hsys.cover c v hab' hvΓ
      exact mem_iUnion.mpr ⟨i, v, hi, hc⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.mp (hv.resolve_right hab')
    rw [hP.v2_eq j] at hj
    obtain ⟨i, hi⟩ := mem_iUnion.mp
      ((Side.supportGraph_subset_iUnion (hsys.coverV j) (hsys.coverS j)).1 hj)
    exact mem_iUnion.mpr ⟨i, v, hi, nm2_eq_of_notMem (fun h' => hab' (Or.inl h'))
      fun d hd => hab' (Or.inr (splitName_mem_splitB_iff'.mp hd).1)⟩

/-- **The split graph has an exhaustive vital `(p + 4q)`-linkage**: (2.4) once for each split
vertex. -/
theorem isExhaustiveLinkage_cut (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) {a b : S}
    (ha : a ∈ Γ.V ∩ bd S) (hb : b ∈ Γ.V ∩ bd S) (hab : a ≠ b) {cb : Bool} {Apf Bpf : Set S}
    {r₂ : ℕ} {P : Fin r₂ → Set S} {τ : Fin r₂ → Fin r} {col : Fin r₂ → Bool × Bool}
    (hsys : IsPieceSystem G Γ Γ_sub μ F_star a b cb Apf Bpf P τ col) (Ea Eb : Set β)
    {K : Hypergraph (Name2 α) β}
    (hK : K ≤ split2 G (μ (.vertex a)).vertexSet Ea (splitB μ a b cb) Eb)
    (hKE : K.edgeSet ⊆ Γ_sub.edgeSet) {L : Hypergraph α β} {p qq : ℕ} (hqq : ∀ j, q j ≤ qq)
    (hL : IsExhaustiveLinkage G Γ_sub r H L) (hLp : IsPLinkage G L p) :
    IsExhaustiveLinkage (split2 G (μ (.vertex a)).vertexSet Ea (splitB μ a b cb) Eb) K r₂
        (fun i => isoImage (nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (col i)) id
          (supportGraph G Γ μ (P i)))
        (splitSpanningSubgraph (split2 G (μ (.vertex a)).vertexSet Ea (splitB μ a b cb) Eb)
          (isoImage Sum.inl id (splitSpanningSubgraph (splitAlong G (μ (.vertex a)).vertexSet Ea)
            (isoImage Sum.inl id L)))) ∧
      IsPLinkage (split2 G (μ (.vertex a)).vertexSet Ea (splitB μ a b cb) Eb)
        (splitSpanningSubgraph (split2 G (μ (.vertex a)).vertexSet Ea (splitB μ a b cb) Eb)
          (isoImage Sum.inl id (splitSpanningSubgraph (splitAlong G (μ (.vertex a)).vertexSet Ea)
            (isoImage Sum.inl id L)))) (p + 4 * qq) := by
  classical
  have hXafin : (μ (.vertex a)).vertexSet.Finite := (μ (.vertex a)).vertexSet_finite
  have hXbfin : (splitB μ a b cb).Finite := (μ (.vertex b)).vertexSet_finite.image _
  obtain ⟨ja, hja⟩ := mem_iUnion.mp (hP.bd_vertices_covered ha)
  obtain ⟨jb, hjb⟩ := mem_iUnion.mp (hP.bd_vertices_covered hb)
  have hμa := hP.μ_vertex_sub ja a ⟨ha.1, hja⟩
  have hμb := hP.μ_vertex_sub jb b ⟨hb.1, hjb⟩
  have hXaG : (μ (.vertex a)).vertexSet ⊆ G.vertexSet :=
    (hμa.1.trans (hP.v1_sub ja)).vertexSet_subset
  have hμbG : (μ (.vertex b)).vertexSet ⊆ G.vertexSet :=
    (hμb.1.trans (hP.v1_sub jb)).vertexSet_subset
  obtain ⟨hV₁, hT₁⟩ := isVitalPLinkage_splitAlong ⟨hL.1, hLp⟩ hXafin.toFinset
    (by rw [hXafin.coe_toFinset]; exact hXaG) Ea
  rw [hXafin.coe_toFinset] at hV₁ hT₁
  obtain ⟨hV₂, hT₂⟩ := isVitalPLinkage_splitAlong hV₁ hXbfin.toFinset (by
    rw [hXbfin.coe_toFinset]
    rintro _ ⟨v, hv, rfl⟩
    exact splitName_mem cb (hμbG hv)) Eb
  rw [hXbfin.coe_toFinset] at hV₂ hT₂
  have hca : hXafin.toFinset.card ≤ qq := by
    rw [← ncard_eq_toFinset_card _ hXafin, hμa.2.2.1]
    exact hqq ja
  have hcb : hXbfin.toFinset.card ≤ qq := by
    rw [← ncard_eq_toFinset_card _ hXbfin]
    exact (ncard_image_le (μ _).vertexSet_finite).trans (hμb.2.2.1 ▸ hqq jb)
  refine ⟨⟨hV₂.1, le_splitSpanningSubgraph hK ?_, ?_⟩,
    ClaimFour.IsPLinkage.mono hV₂.2 (by omega)⟩
  · intro e he
    exact ⟨e, ⟨hK.edgeSet_subset he, e, hL.2.1.edgeSet_subset (hKE he), rfl⟩, rfl⟩
  · intro t ht
    obtain ⟨c, v, -, rfl⟩ := exists_nm2_of_mem (G := G) (Ea := Ea) (Eb := Eb) ht.1
    refine nm2_mem_pieces hP ha hb hab hsys c ?_
    rcases hT₂ ht with (⟨t₁, ht₁, hte⟩ | ⟨w, hw, hwe⟩) | ⟨w, hw, hwe⟩
    · have h1 : splitName (μ (.vertex a)).vertexSet c.1 v = t₁ := (splitName_eq_inl hte.symm).1
      rcases hT₁ ht₁ with (⟨t₀, ht₀, hte₀⟩ | ⟨w, hw, hwe⟩) | ⟨w, hw, hwe⟩
      · have h0 : v = t₀ := (splitName_eq_inl (h1.trans hte₀.symm)).1
        exact Or.inl (h0 ▸ hL.2.2 ht₀)
      · exact Or.inr (Or.inl (eq_of_splitName_eq_inr_inl (h1.trans hwe.symm) ▸ hw))
      · exact Or.inr (Or.inl (eq_of_splitName_eq_inr_inr (h1.trans hwe.symm) ▸ hw))
    · have h1 := eq_of_splitName_eq_inr_inl hwe.symm
      exact Or.inr (Or.inr (splitName_mem_splitB_iff'.mp (h1 ▸ hw)).1)
    · have h1 := eq_of_splitName_eq_inr_inr hwe.symm
      exact Or.inr (Or.inr (splitName_mem_splitB_iff'.mp (h1 ▸ hw)).1)

end CutLine
end GM21
end GraphMinor
