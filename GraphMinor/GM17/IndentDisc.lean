module

public import GraphMinor.GM17.IndentPaint
public import GraphMinor.GM17.IndentPush
public import GraphMinor.Surface.DiscUnion
import GraphMinor.GM17.CellNodes

/-!
# Pushing a node to a cuff across a disc

Let `D` be a closed disc whose boundary is a line `A` of a cuff and a line `G` through an internal node `n`, and suppose that `D` has
no nodes but `n` and the two ends. This is the disc `Δ₀ ∪ Δ₁ ∪ Δ₂` of the proof of (9.3) of Graph Minors XVII, page 184, and the disc
`Δ ∪ Δ₁ ∪ Δ₂` of the proof of (9.4), page 185. We remove `D` from the surface, in the paper's words, and show that what is left is the
surface again. A larger disc `B` around `D` has no further nodes (`exists_ring_sub`). Now `closure (B \ D)` is a closed disc with boundary
`K ∪ G`, and `B` has a closed disc with boundary `K ∪ E` for a line `E` from an end of `A` to a point `n'` of `A` and on to the other
end. So we can map one disc onto the other, fixing `K` and moving `n` to `n'` (`exists_disc_map`), and this gives the new painting
(`indented_of_disc`). The rest of `B` is two discs `T₁`, `T₂` along `A`. They are the two new cells.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology Metric GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

theorem indented_of_disc [ConnectedSpace S] (hS : IsSurface S) (Γ : Painting S) {D A G Θ c₀ : Set S} {n n₁ n₂ n' : S} {R : Set (Set S)}
    (hD : IsClosedDisc D) (hA : IsLineWithEnds A n₁ n₂) (hG : IsLineWithEnds G n₁ n₂) (hbD : discBd D = A ∪ G) (hAG : A ∩ G = {n₁, n₂})
    (hDb : D ∩ bd S = A) (hDN : D ∩ Γ.N = {n₁, n₂, n}) (hnG : n ∈ G \ {n₁, n₂}) (hnb : n ∉ bd S) (hn'A : n' ∈ A \ {n₁, n₂})
    (hn'c : n' ∈ c₀ ∩ Θ) (hAΘ : A ⊆ Θ)
    (hRsub : ∀ c ∈ Γ.C, c ∈ R → c ⊆ D) (hRd : ∀ c ∈ Γ.C, c ∉ R → Disjoint c D) :
    ∃ Γ' : Painting S, IsIndentedBorderPainting Γ Θ c₀ n₁ n₂ n R Γ' := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  have hne : n₁ ≠ n₂ := hA.ne'
  have hAD : A ⊆ D := fun x hx => discBd_subset _ (hbD ▸ .inl hx)
  have hGD : G ⊆ D := fun x hx => discBd_subset _ (hbD ▸ .inr hx)
  have hAb : A ⊆ bd S := fun x hx => (hDb ▸ hx : x ∈ D ∩ bd S).2
  have hnodes : ∀ {x}, x ∈ ({n₁, n₂, n} : Set S) → x ∈ D ∧ x ∈ Γ.N := fun hx => hDN.symm.subset hx
  have hn₁N : n₁ ∈ Γ.N := (hnodes (.inl rfl)).2
  have hn₂N : n₂ ∈ Γ.N := (hnodes (.inr (.inl rfl))).2
  have hnN : n ∈ Γ.N := (hnodes (.inr (.inr rfl))).2
  have hn₁ : n₁ ≠ n := fun h => hnG.2 (.inl h.symm)
  have hn₂ : n₂ ≠ n := fun h => hnG.2 (.inr h.symm)
  let Z : Set S := (Γ.N \ {n}) ∪ bd S
  have hZc : IsClosed Z := (Γ.finite_N.subset sdiff_subset).isClosed.union (isClosed_bd S)
  have hZD : Z ∩ D = A := by
    ext x
    constructor
    · rintro ⟨(⟨hx, hxn⟩ | hx), hxD⟩
      · have h3 : x ∈ D ∩ Γ.N := ⟨hxD, hx⟩
        rw [hDN] at h3
        rcases h3 with rfl | rfl | h3
        · exact hA.left_mem
        · exact hA.right_mem
        · exact absurd h3 hxn
      · exact hDb ▸ ⟨hxD, hx⟩
    · intro hx
      exact ⟨.inr (hAb hx), hAD hx⟩
  obtain ⟨B, hB, hDB, hBZ, hbB, hBb⟩ := exists_ring_sub hS hD hZc
    (by rw [hZD, hbD]; exact subset_union_left) (fun x hx => .inr hx.2)
  rw [inter_comm D Z, hZD] at hBZ hbB
  rw [hDb] at hBb
  have hAdB : A ⊆ discBd B := fun x hx => by
    have h3 : x ∈ A := hx
    rw [← hbB] at h3
    exact h3.1
  have hbI : discBd D ∩ discBd B = A := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ⟨hbD ▸ .inl hx, hAdB hx⟩
    exact hbB ▸ (⟨hx.2, discBd_subset _ hx.1⟩ : x ∈ discBd B ∩ D)
  obtain ⟨K, hK, hAK, hAK'⟩ := oarc_split hB.isOArc_discBd hA hAdB
  have hKdB : K ⊆ discBd B := fun x hx => hAK ▸ .inr hx
  have hKnotA : ∀ {x}, x ∈ K → x ∈ A → x = n₁ ∨ x = n₂ := fun {x} hx hx' => (hAK' ▸ ⟨hx', hx⟩ : x ∈ ({n₁, n₂} : Set S))
  have hGnotA : ∀ {x}, x ∈ G → x ∈ A → x = n₁ ∨ x = n₂ := fun {x} hx hx' => (hAG ▸ ⟨hx', hx⟩ : x ∈ ({n₁, n₂} : Set S))
  obtain ⟨hQ, hbQ, hQD⟩ := disc_difference D B A n₁ n₂ hD hB hDB hA hbI
  set Q := closure (B \ D) with hQdef
  have hQB : Q ⊆ B := closure_minimal sdiff_subset hB.isClosed
  have hBU : ∀ {x}, x ∈ B → x ∈ Q ∨ x ∈ D := fun {x} hx => by
    by_cases h : x ∈ D
    · exact .inr h
    · exact .inl (subset_closure ⟨hx, h⟩)
  have hxA : ∀ {x}, x ∉ A \ {n₁, n₂} → x ∈ A → x = n₁ ∨ x = n₂ := fun hx h3 => by_contra fun h4 => hx ⟨h3, h4⟩
  have hbQK : discBd Q = K ∪ G := by
    rw [hbQ, hbD, ← hAK]
    ext x
    constructor
    · rintro ⟨((h | h) | (h | h)), hx⟩
      · rcases hxA hx h with rfl | rfl
        · exact .inl hK.left_mem
        · exact .inl hK.right_mem
      · exact .inr h
      · rcases hxA hx h with rfl | rfl
        · exact .inl hK.left_mem
        · exact .inl hK.right_mem
      · exact .inl h
    · rintro (h | h)
      · exact ⟨.inr (.inr h), fun h3 => h3.2 (hKnotA h h3.1)⟩
      · exact ⟨.inl (.inr h), fun h3 => h3.2 (hGnotA h h3.1)⟩
  have hQDG : Q ∩ D = G := by
    rw [hQD, hbD]
    ext x
    constructor
    · rintro ⟨(h | h), hx⟩
      · rcases hxA hx h with rfl | rfl
        · exact hG.left_mem
        · exact hG.right_mem
      · exact h
    · intro h
      exact ⟨.inr h, fun h3 => h3.2 (hGnotA h h3.1)⟩
  have hKQ : K ⊆ Q := fun x hx => discBd_subset _ (hbQK ▸ .inl hx)
  have hGQ : G ⊆ Q := fun x hx => discBd_subset _ (hbQK ▸ .inr hx)
  -- The cells along `A`, and the disc `Q'`.
  have hn'1 : n' ≠ n₁ := fun h => hn'A.2 (.inl h)
  have hn'2 : n' ≠ n₂ := fun h => hn'A.2 (.inr h)
  obtain ⟨A₁, A₂, hA₁, hA₂, hAu, hAi⟩ := hA.split hn'A.1 hn'1 hn'2
  have hA₁A : A₁ ⊆ A := hAu ▸ subset_union_left
  have hA₂A : A₂ ⊆ A := hAu ▸ subset_union_right
  have hKA₂ : K ∩ A₂ = {n₂} := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · rcases hKnotA hx.1 (hA₂A hx.2) with rfl | rfl
      · have h3 : x ∈ A₁ ∩ A₂ := ⟨hA₁.left_mem, hx.2⟩
        rw [hAi] at h3
        exact absurd h3.symm hn'1
      · rfl
    · rintro x rfl
      exact ⟨hK.right_mem, hA₂.right_mem⟩
  have hC₁ : IsLineWithEnds (K ∪ A₂) n₁ n' := hK.union hA₂.symm hKA₂
  have hsplitB : A₁ ∪ (K ∪ A₂) = discBd B := by
    rw [← hAK, ← hAu]
    ext x
    simp only [mem_union]
    tauto
  have hiB : A₁ ∩ (K ∪ A₂) = {n₁, n'} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx, (h | h)⟩
      · rcases hKnotA h (hA₁A hx) with rfl | rfl
        · exact .inl rfl
        · exact absurd (show x ∈ A₁ ∩ A₂ from ⟨hx, hA₂.right_mem⟩) (by rw [hAi]; exact hn'2.symm)
      · exact .inr (hAi ▸ ⟨hx, h⟩ : x ∈ ({n'} : Set S))
    · rintro x (rfl | rfl)
      · exact ⟨hA₁.left_mem, .inl hK.left_mem⟩
      · exact ⟨hA₁.right_mem, .inr hA₂.left_mem⟩
  obtain ⟨E₁, T₁, R₁, hE₁, hE₁b, hE₁B, hT₁, hR₁, huB, hiB₁, hbT₁, hbR₁⟩ := split_disc hB hA₁ hC₁ hn'1.symm hsplitB hiB
  have hKE₁ : E₁ ∩ K = {n₁} := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · have h3 : x ∈ E₁ ∩ discBd B := ⟨hx.1, hKdB hx.2⟩
      rw [hE₁b] at h3
      rcases h3 with rfl | rfl
      · rfl
      · rcases hKnotA hx.2 hn'A.1 with h | h
        · exact absurd h hn'1
        · exact absurd h hn'2
    · rintro x rfl
      exact ⟨hE₁.left_mem, hK.left_mem⟩
  have hC₂ : IsLineWithEnds (E₁ ∪ K) n' n₂ := hE₁.symm.union hK hKE₁
  have hbR : A₂ ∪ (E₁ ∪ K) = discBd R₁ := by
    rw [hbR₁]
    ext x
    simp only [mem_union]
    tauto
  have hn₂E₁ : n₂ ∉ E₁ := fun h => by
    have h3 : n₂ ∈ E₁ ∩ discBd B := ⟨h, hKdB hK.right_mem⟩
    rw [hE₁b] at h3
    rcases h3 with h3 | h3
    · exact hne h3.symm
    · exact hn'2 h3.symm
  have hiR : A₂ ∩ (E₁ ∪ K) = {n', n₂} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx, (h | h)⟩
      · have h3 : x ∈ E₁ ∩ discBd B := ⟨h, hAdB (hA₂A hx)⟩
        rw [hE₁b] at h3
        rcases h3 with rfl | rfl
        · exact absurd (show x ∈ A₁ ∩ A₂ from ⟨hA₁.left_mem, hx⟩) (by rw [hAi]; exact hn'1.symm)
        · exact .inl rfl
      · exact .inr (hKA₂ ▸ ⟨h, hx⟩ : x ∈ ({n₂} : Set S))
    · rintro x (rfl | rfl)
      · exact ⟨hA₂.left_mem, .inl hE₁.right_mem⟩
      · exact ⟨hA₂.right_mem, .inr hK.right_mem⟩
  obtain ⟨E₂, T₂, Q', hE₂, hE₂b, hE₂R, hT₂, hQ', huR, hiR₂, hbT₂, hbQ'⟩ := split_disc hR₁ hA₂ hC₂ hn'2 hbR hiR
  have hE₁Q' : E₁ ⊆ Q' := fun x hx => discBd_subset _ (hbQ' ▸ .inl (.inl hx))
  have hE₁dR : E₁ ⊆ discBd R₁ := fun x hx => hbR₁ ▸ .inr hx
  have hKdR : K ⊆ discBd R₁ := fun x hx => hbR₁ ▸ .inl (.inl hx)
  have hE₁₂ : E₁ ∩ E₂ = {n'} := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · have h3 : x ∈ E₂ ∩ discBd R₁ := ⟨hx.2, hE₁dR hx.1⟩
      rw [hE₂b] at h3
      rcases h3 with rfl | rfl
      · rfl
      · exact absurd hx.1 hn₂E₁
    · rintro x rfl
      exact ⟨hE₁.right_mem, hE₂.left_mem⟩
  have hE : IsLineWithEnds (E₁ ∪ E₂) n₁ n₂ := hE₁.union hE₂ hE₁₂
  have hbQE : discBd Q' = K ∪ (E₁ ∪ E₂) := by
    rw [hbQ']
    ext x
    simp only [mem_union]
    tauto
  have hKE : K ∩ (E₁ ∪ E₂) = {n₁, n₂} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx, (h | h)⟩
      · exact .inl (hKE₁ ▸ ⟨h, hx⟩ : x ∈ ({n₁} : Set S))
      · have h3 : x ∈ E₂ ∩ discBd R₁ := ⟨h, hKdR hx⟩
        rw [hE₂b] at h3
        rcases h3 with rfl | rfl
        · rcases hKnotA hx hn'A.1 with h4 | h4
          · exact absurd h4 hn'1
          · exact absurd h4 hn'2
        · exact .inr rfl
    · rintro x (rfl | rfl)
      · exact ⟨hK.left_mem, .inl hE₁.left_mem⟩
      · exact ⟨hK.right_mem, .inr hE₂.right_mem⟩
  have hn'E : n' ∈ (E₁ ∪ E₂) \ {n₁, n₂} := by
    refine ⟨.inl hE₁.right_mem, ?_⟩
    rintro (h | h)
    · exact hn'1 h
    · exact hn'2 h
  obtain ⟨f, hfc, hfi, hfQ, hfK, hfn, hfG⟩ := exists_disc_map hQ hQ' hK hG hE hbQK hbQE (by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · have h3 : x ∈ Q ∩ D := ⟨hKQ hx.1, hGD hx.2⟩
      have h4 : x ∈ discBd B ∩ D := ⟨hKdB hx.1, h3.2⟩
      rw [hbB] at h4
      exact hKnotA hx.1 h4
    · rintro x (rfl | rfl)
      · exact ⟨hK.left_mem, hG.left_mem⟩
      · exact ⟨hK.right_mem, hG.right_mem⟩) hKE hnG hn'E
  have hR₁B : R₁ ⊆ B := huB ▸ subset_union_right
  have hT₁B : T₁ ⊆ B := huB ▸ subset_union_left
  have hQ'R : Q' ⊆ R₁ := huR ▸ subset_union_right
  have hT₂R : T₂ ⊆ R₁ := huR ▸ subset_union_left
  have hQ'B : Q' ⊆ B := hQ'R.trans hR₁B
  have hKb : K ∩ bd S = {n₁, n₂} := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · have h3 : x ∈ B ∩ bd S := ⟨discBd_subset _ (hKdB hx.1), hx.2⟩
      rw [hBb] at h3
      exact hKnotA hx.1 h3
    · rintro x (rfl | rfl)
      · exact ⟨hK.left_mem, hAb hA.left_mem⟩
      · exact ⟨hK.right_mem, hAb hA.right_mem⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hnbB⟩ := arc_disc_data hS hK hKb hB hKdB (fun x hx => by
    rw [← hAK] at hx
    rcases hx with h | h
    · exact .inr (hAb h)
    · exact .inl h)
  have hclB : ∀ x, x ∈ closure Bᶜ → x ∈ B → x ∈ K := fun x hx hxB => by
    by_contra h
    obtain ⟨y, hy, hy'⟩ := mem_closure_iff_nhds.mp hx _ (hnbB x ⟨hxB, h⟩)
    exact hy' hy
  let W : Set S := Q ∪ Bᶜ
  have hWU : W = Q ∪ closure Bᶜ := by
    refine Subset.antisymm (union_subset_union_right _ subset_closure) (union_subset subset_union_left fun x hx => ?_)
    by_cases h : x ∈ B
    · exact .inl (hKQ (hclB x hx h))
    · exact .inr h
  have hWc : IsClosed W := by
    rw [hWU]
    exact hQ.isClosed.union isClosed_closure
  let φ : S → S := fun x => if x ∈ Q then f x else x
  have hφQ : ∀ x ∈ Q, φ x = f x := fun x hx => by simp only [φ, hx, ite_true]
  have hφO : ∀ x, x ∉ Q → φ x = x := fun x hx => by simp only [φ, hx, ite_false]
  have hφc : ContinuousOn φ W := by
    rw [hWU]
    refine ContinuousOn.union_of_isClosed (hfc.congr hφQ) (continuousOn_id.congr fun x hx => ?_) hQ.isClosed isClosed_closure
    by_cases h : x ∈ Q
    · by_cases hxB : x ∈ B
      · rw [hφQ x h, hfK x (hclB x hx hxB)]
        rfl
      · exact absurd (hQB h) hxB
    · exact hφO x h
  have hfm : ∀ {x}, x ∈ Q → f x ∈ Q' := fun hx => hfQ ▸ mem_image_of_mem f hx
  have hφi : InjOn φ W := by
    rintro x (hx | hx) y (hy | hy) hxy
    · rw [hφQ x hx, hφQ y hy] at hxy
      exact hfi hx hy hxy
    · rw [hφQ x hx, hφO y fun h => hy (hQB h)] at hxy
      exact absurd (hQ'B (hxy ▸ hfm hx)) hy
    · rw [hφQ y hy, hφO x fun h => hx (hQB h)] at hxy
      exact absurd (hQ'B (hxy.symm ▸ hfm hy)) hx
    · rwa [hφO x fun h => hx (hQB h), hφO y fun h => hy (hQB h)] at hxy
  have hA₁T : A₁ ⊆ T₁ := fun x hx => discBd_subset _ (hbT₁ ▸ .inl hx)
  have hA₂T : A₂ ⊆ T₂ := fun x hx => discBd_subset _ (hbT₂ ▸ .inl hx)
  have hT : T₁ ∩ T₂ = {n'} := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · have h3 : x ∈ E₁ := hiB₁ ▸ ⟨hx.1, hT₂R hx.2⟩
      have h4 : x ∈ E₂ := hiR₂ ▸ ⟨hx.2, hE₁Q' h3⟩
      exact hE₁₂ ▸ ⟨h3, h4⟩
    · rintro x rfl
      exact ⟨hA₁T hA₁.right_mem, hA₂T hA₂.left_mem⟩
  have hB_A : ∀ {x}, x ∈ B → x ∈ bd S → x ∈ A := fun {x} hx hb => (hBb ▸ ⟨hx, hb⟩ : x ∈ A)
  have hb₁ : T₁ ∩ bd S = A₁ := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ⟨hA₁T hx, hAb (hA₁A hx)⟩
    have h3 : x ∈ A₁ ∪ A₂ := hAu ▸ hB_A (hT₁B hx.1) hx.2
    rcases h3 with h3 | h3
    · exact h3
    · have h4 : x = n' := hT.subset ⟨hx.1, hA₂T h3⟩
      exact h4 ▸ hA₁.right_mem
  have hb₂ : T₂ ∩ bd S = A₂ := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ⟨hA₂T hx, hAb (hA₂A hx)⟩
    have h3 : x ∈ A₁ ∪ A₂ := hAu ▸ hB_A (hR₁B (hT₂R hx.1)) hx.2
    rcases h3 with h3 | h3
    · have h4 : x = n' := hT.subset ⟨hA₁T h3, hx.1⟩
      exact h4 ▸ hA₂.left_mem
    · exact h3
  have hBN : ∀ {x}, x ∈ B → x ∈ Γ.N \ {n} → x = n₁ ∨ x = n₂ := fun {x} hx hxN => by
    have h3 : x ∈ A := hBZ ▸ (⟨hx, .inl hxN⟩ : x ∈ B ∩ Z)
    have h4 : x ∈ D ∩ Γ.N := ⟨hAD h3, hxN.1⟩
    rw [hDN] at h4
    rcases h4 with h4 | h4 | h4
    · exact .inl h4
    · exact .inr h4
    · exact absurd h4 hxN.2
  have hfiber : ∀ {y}, y ∈ Q → y ∉ D → f y ∉ E₁ ∪ E₂ := fun {y} hy hyD hm => by
    obtain ⟨g, hg, hgy⟩ := hfG.symm.subset hm
    exact hyD (hfi (hGQ hg) hy hgy ▸ hGD hg)
  have hoff : ∀ y, y ∉ D → φ y ∉ T₁ ∧ φ y ∉ T₂ := fun y hyD => by
    by_cases hy : y ∈ Q
    · rw [hφQ y hy]
      refine ⟨fun h => hfiber hy hyD (.inl (hiB₁ ▸ ⟨h, hQ'R (hfm hy)⟩)), fun h => hfiber hy hyD (.inr (hiR₂ ▸ ⟨h, hfm hy⟩))⟩
    · rw [hφO y hy]
      have hyB : y ∉ B := fun h => (hBU h).elim hy hyD
      exact ⟨fun h => hyB (hT₁B h), fun h => hyB (hR₁B (hT₂R h))⟩
  refine indented_of_push Γ (W := W) (D := D) (T₁ := T₁) (T₂ := T₂) (A₁ := A₁) (A₂ := A₂) (φ := φ) (n' := n') hWc hD.isClosed
    (fun x hx => ?_) hφc hφi hnN (.inl (hGQ hnG.1)) hn₁N hn₂N hn₁ hn₂ ?_ ((hφQ n (hGQ hnG.1)).trans hfn) hnb ?_ hn'c
    hRsub hRd hT₁ hT₂ hA₁ hA₂.symm (fun x hx => hbT₁ ▸ .inl hx) (fun x hx => hbT₂ ▸ .inl hx) hb₁ hb₂ (hA₁A.trans hAΘ) (hA₂A.trans hAΘ) hT
    ?_ ?_ hoff ?_ ?_
  · by_cases h : x ∈ B
    · exact .inl ((hBU h).resolve_right hx)
    · exact .inr h
  · intro x hx hxn
    by_cases hxB : x ∈ B
    · have hxK : x ∈ K := by
        rcases hBN hxB ⟨hx, hxn⟩ with rfl | rfl
        · exact hK.left_mem
        · exact hK.right_mem
      exact ⟨.inl (hKQ hxK), (hφQ x (hKQ hxK)).trans (hfK x hxK)⟩
    · exact ⟨.inr hxB, hφO x fun h => hxB (hQB h)⟩
  · intro h
    have h3 : n' ∈ D ∩ Γ.N := ⟨hAD hn'A.1, h⟩
    rw [hDN] at h3
    rcases h3 with h3 | h3 | h3
    · exact hn'1 h3
    · exact hn'2 h3
    · exact hnb (h3 ▸ hAb hn'A.1)
  · rintro x ⟨hx, hxN⟩
    rcases hBN (hT₁B hx) hxN with h | h
    · exact h
    · subst h
      have h4 : x = n' := hT.subset ⟨hx, hA₂T hA₂.right_mem⟩
      exact absurd h4.symm hn'2
  · rintro x ⟨hx, hxN⟩
    rcases hBN (hR₁B (hT₂R hx)) hxN with h | h
    · subst h
      have h4 : x = n' := hT.subset ⟨hA₁T hA₁.left_mem, hx⟩
      exact absurd h4.symm hn'1
    · exact h
  · intro y hyD hb
    by_cases hy : y ∈ Q
    · exfalso
      rcases hb with hb | hb
      · exact hyD (hAD (hB_A (hQB hy) hb))
      · rw [hφQ y hy] at hb
        have h3 := hB_A (hQ'B (hfm hy)) hb
        have h4 := hoff y hyD
        rw [hφQ y hy] at h4
        rw [← hAu] at h3
        rcases h3 with h3 | h3
        · exact h4.1 (hA₁T h3)
        · exact h4.2 (hA₂T h3)
    · exact hφO y hy
  · intro x hx
    by_cases hxB : x ∈ B
    · have h3 : x ∈ A₁ ∪ A₂ := hAu ▸ hB_A hxB hx
      rcases h3 with h3 | h3
      · exact .inl (hA₁T h3)
      · exact .inr (.inl (hA₂T h3))
    · exact .inr (.inr ⟨fun h => hxB (hDB h), hφO x fun h => hxB (hQB h)⟩)

end GraphMinor.GM17
