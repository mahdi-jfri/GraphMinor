module

public import GraphMinor.GM08.Section18ClassD
public import GraphMinor.GM08.Section18ListSum
import GraphMinor.GM08.Section18ClopenSplit
import GraphMinor.GM08.Section18ClopenComplexity
public import GraphMinor.GM08.Section11Iso
import GraphMinor.GM08.Section13
import GraphMinor.GM08.Section4
import GraphMinor.GM08.Section14
import GraphMinor.Surface.CutComp

/-!
# The union over components, page 288 of VIII

A graft drawn in a surface `Σ` splits along the components of `Σ`. We split
off the component of one point at a time (`exists_component_split`). The piece
in that component lies in `𝒟(g(Σ), ·)`, and the rest is drawn in the other
components, which form a surface with no larger `g`.

- A rootless graft is a sum of a list of members of `𝒟(h, 0)`
  (`exists_listSum_classD`). So `𝒞(h, 0)` is well-rooted when `𝒟(h, 0)` is,
  by (3.3) (`isWellRooted_classC_zero`).
- A graft of index at most `j` lies in `classEPad h k j`: at most `j` summands
  from `𝒟(h, k)`, plus a member of `𝒞(h, 0)`. This is the class
  `𝓔(h, k) ⊕ 𝒞(h, 0)` of the paper, except that we allow fewer than `k`
  summands instead of padding with empty grafts. So `𝒞(h, k)` is well-rooted
  when `𝒟(h, k)` and `𝒞(h, 0)` are, by (13.1) and (4.2)
  (`isWellRooted_classC_of_classD`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Graph GraphMinor.Surface

universe u v w

/-- `𝒟(h, k)` grows with `h` and `k`. -/
theorem classD_mono {α : Type u} {β : Type v} {h h' k k' : ℕ} (hh : h ≤ h') (hk : k ≤ k') :
    classD.{u, v, w} (α := α) (β := β) h k ⊆ classD.{u, v, w} h' k' := by
  rintro X ⟨S, tS, hS, hc, hg, hX, hE⟩
  exact ⟨S, tS, hS, hc, hg.trans hh, hX.trans hk, hE⟩

/-- **The piece of a graft in the component of a point.** The graft is a
direct sum of a piece in `𝒟(g(Σ), ·)`, drawn in the component of `p`, and a
rest drawn in a surface with no larger `g`. -/
theorem exists_component_split {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    [Nonempty S] (hS : IsSurface S) {X : Graft α β} (gd : GraftDrawing X.G X.T S) (p : S) :
    ∃ A B : Graft α β, IsGraftDirectSum X A B ∧
      A ∈ classD.{u, v, w} (surfaceComplexity S) A.index ∧
      (∃ (K : Type w) (_ : TopologicalSpace K), IsSurface K ∧
        surfaceComplexity K ≤ surfaceComplexity S ∧ EmbedsGraft K B) ∧
      A.T = X.T ∩ {v ∈ V(X.G) | gd.iso.fv v ∈ connectedComponent p} ∧
      V(A.G) = {v ∈ V(X.G) | gd.iso.fv v ∈ connectedComponent p} := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  have hK : IsClopen (connectedComponent p) := isClopen_connectedComponent
  obtain ⟨A, B, hsum, hA, hB, hAT, hAG⟩ := exists_clopen_split gd hK
  have hconn : ConnectedSpace (connectedComponent p) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  refine ⟨A, B, hsum, ⟨connectedComponent p, inferInstance, isSurface_sub hS hK, hconn,
    surfaceComplexity_le_of_isClopen hS hK, le_rfl, hA⟩,
    ⟨((connectedComponent p)ᶜ : Set S), inferInstance, isSurface_sub hS hK.compl,
      surfaceComplexity_le_of_isClopen hS hK.compl, hB⟩, hAT, by simp [hAG]⟩

/-- The rest of a direct sum has the other vertices. -/
theorem IsGraftDirectSum.vertexSet_right {α : Type u} {β : Type v} {X A B : Graft α β}
    (h : IsGraftDirectSum X A B) : V(B.G) = V(X.G) \ V(A.G) := by
  obtain ⟨Y, hY, -, hA, hB, -, -⟩ := h
  simp [hB, hA]

/-- The roots of the rest of a direct sum are the other roots. -/
theorem IsGraftDirectSum.T_right_ssubset {α : Type u} {β : Type v} {X A B : Graft α β}
    (h : IsGraftDirectSum X A B) {t : α} (ht : t ∈ A.T) : B.T ⊂ X.T := by
  obtain ⟨Y, -, -, -, -, hA, hB⟩ := h
  rw [hB]
  rw [hA] at ht
  exact ssubset_of_subset_not_subset sdiff_subset fun hsub => (hsub ht.1).2 ht.2

/-- **A rootless graft is a sum of members of `𝒟(g(Σ), 0)`.** -/
theorem exists_listSum_classD {α : Type u} {β : Type v} (n : ℕ) :
    ∀ {S : Type w} [TopologicalSpace S], IsSurface S → ∀ {X : Graft α β},
      GraftDrawing X.G X.T S → X.T = ∅ → V(X.G).ncard ≤ n →
      ∃ L : List (Graft α β), IsGraftListSum X L ∧
        ∀ A ∈ L, A ∈ classD.{u, v, w} (surfaceComplexity S) 0 := by
  induction n with
  | zero =>
    intro S _ _ X _ _ hn
    have hV : V(X.G) = ∅ := (ncard_eq_zero X.finite_G.1).mp (Nat.le_zero.mp hn)
    exact ⟨[], IsGraftListSum.nil hV, by simp⟩
  | succ n ih =>
    intro S _ hS X gd hT hn
    rcases V(X.G).eq_empty_or_nonempty with hV | ⟨v, hv⟩
    · exact ⟨[], IsGraftListSum.nil hV, by simp⟩
    have : Nonempty S := ⟨(gd.iso.vertexEquiv ⟨v, hv⟩).1⟩
    obtain ⟨A, B, hsum, hA, ⟨K, tK, hK, hKg, ⟨gdB⟩⟩, hAT, hAV⟩ :=
      exists_component_split hS gd (gd.iso.fv v)
    have hvA : v ∈ V(A.G) := by rw [hAV]; exact ⟨hv, mem_connectedComponent⟩
    have hBV : V(B.G).ncard ≤ n := by
      have hlt : V(B.G).ncard < V(X.G).ncard := by
        rw [hsum.vertexSet_right]
        exact ncard_lt_ncard (ssubset_of_subset_not_subset sdiff_subset
          fun hsub => (hsub hv).2 hvA) X.finite_G.1
      omega
    obtain ⟨L, hL, hLD⟩ := ih hK gdB (hsum.T_right_eq_empty hT) hBV
    have hAT0 : A.index = 0 := by
      rw [Graft.index, hsum.T_left_eq_empty hT, ncard_empty]
    refine ⟨A :: L, IsGraftListSum.cons hsum hL, ?_⟩
    intro A' hA'
    rcases List.mem_cons.1 hA' with rfl | hA'
    · rw [hAT0] at hA
      exact hA
    · exact classD_mono hKg le_rfl (hLD A' hA')

/-- **`𝒞(h, 0)` is well-rooted** if `𝒟(h, 0)` is, by (3.3): its members are
sums of members of `𝒟(h, 0)`. -/
theorem isWellRooted_classC_zero {α : Type u} {β : Type v} {h : ℕ}
    (hD : IsWellRootedGraftClass (classD.{u, v, w} (α := α) (β := β) h 0)) :
    IsWellRootedGraftClass (classC.{u, v, w} (α := α) (β := β) h 0) := by
  refine isWellRooted_of_listSum hD fun X hX => ?_
  obtain ⟨S, tS, hS, hg, hX0, ⟨gd⟩⟩ := hX
  have hT : X.T = ∅ :=
    (ncard_eq_zero (X.finite_G.1.subset X.T_subset)).mp (Nat.le_zero.mp hX0)
  obtain ⟨L, hL, hLD⟩ := exists_listSum_classD (V(X.G).ncard) hS gd hT le_rfl
  exact ⟨hT, L, fun A hA => classD_mono hg le_rfl (hLD A hA), hL⟩

/-- At most `j` summands from `𝒟(h, k)`, followed by a member of `𝒞(h, 0)`. -/
def classEPad {α : Type u} {β : Type v} (h k : ℕ) : ℕ → Set (Graft α β)
  | 0 => classC.{u, v, w} h 0
  | j + 1 => graftDirectSumClass (classD.{u, v, w} h k) (classEPad h k j) ∪ classEPad h k j

/-- A graft drawn in a surface with `g ≤ h`, with index at most `j ≤ k`, lies
in `classEPad h k j`. -/
theorem mem_classEPad {α : Type u} {β : Type v} {h k : ℕ} (j : ℕ) :
    ∀ {X : Graft α β}, X ∈ classC.{u, v, w} h k → X.index ≤ j →
      X ∈ classEPad.{u, v, w} h k j := by
  induction j with
  | zero =>
    rintro X ⟨S, tS, hS, hg, -, hE⟩ hj
    exact ⟨S, tS, hS, hg, hj, hE⟩
  | succ j ih =>
    intro X hX hj
    obtain ⟨S, tS, hS, hg, hXk, ⟨gd⟩⟩ := hX
    rcases X.T.eq_empty_or_nonempty with hT | ⟨t, ht⟩
    · refine Or.inr (ih ⟨S, tS, hS, hg, hXk, ⟨gd⟩⟩ ?_)
      rw [Graft.index, hT, ncard_empty]
      exact Nat.zero_le _
    have : Nonempty S := ⟨(gd.iso.vertexEquiv ⟨t, X.T_subset ht⟩).1⟩
    obtain ⟨A, B, hsum, hA, ⟨K, tK, hK, hKg, hB⟩, hAT, -⟩ :=
      exists_component_split hS gd (gd.iso.fv t)
    have htA : t ∈ A.T := by
      rw [hAT]
      exact ⟨ht, X.T_subset ht, mem_connectedComponent⟩
    have hBT : B.T ⊂ X.T := hsum.T_right_ssubset htA
    have hXfin : X.T.Finite := X.finite_G.1.subset X.T_subset
    have hBlt : B.index < X.index := ncard_lt_ncard hBT hXfin
    have hAle : A.index ≤ X.index := by
      rw [Graft.index, Graft.index, hAT]
      exact ncard_le_ncard inter_subset_left hXfin
    refine Or.inl ⟨A, classD_mono hg (hAle.trans hXk) hA, B, ih ⟨K, tK, hK, hKg.trans hg,
      by omega, hB⟩ (by omega), hsum⟩

/-- Each `classEPad h k j` is well-rooted, by (13.1) and (4.2). -/
theorem isWellRooted_classEPad {α : Type u} {β : Type v} {h k : ℕ}
    (hD : IsWellRootedGraftClass (classD.{u, v, w} (α := α) (β := β) h k))
    (hC : IsWellRootedGraftClass (classC.{u, v, w} (α := α) (β := β) h 0)) :
    ∀ j, IsWellRootedGraftClass (classEPad.{u, v, w} (α := α) (β := β) h k j)
  | 0 => hC
  | j + 1 => theorem_4_2_proof (theorem_13_1_proof hD (isWellRooted_classEPad hD hC j))
      (isWellRooted_classEPad hD hC j)

/-- **`𝒞(h, k)` is well-rooted** if `𝒟(h, k)` and `𝒟(h, 0)` are (page 288). -/
theorem isWellRooted_classC_of_classD {α : Type u} {β : Type v} {h k : ℕ}
    (hD : IsWellRootedGraftClass (classD.{u, v, w} (α := α) (β := β) h k))
    (hD0 : IsWellRootedGraftClass (classD.{u, v, w} (α := α) (β := β) h 0)) :
    IsWellRootedGraftClass (classC.{u, v, w} (α := α) (β := β) h k) :=
  isWellRootedGraftClass_mono (fun X hX => mem_classEPad k hX (by
    obtain ⟨_, _, _, _, hk, _⟩ := hX
    exact hk))
    (isWellRooted_classEPad hD (isWellRooted_classC_zero hD0) k)

end GraphMinor.GM08
