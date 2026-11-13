module

public import GraphMinor.Compute.CrossingClassBridgeMath
public import GraphMinor.Compute.CrossingClassPathAllowed

/-!
# Paths inside bridge interiors

At the end of Section 5.2 of `docs/crossing/crossing_extractor.tex`, each of the two path searches
looks inside a component together with its selected endpoints, or uses a chord. This file supplies
the reachability needed by that search and proves that paths with interiors in distinct bridges are
disjoint when their four ends are distinct.
-/

public section

namespace GraphMinor.Compute

open SimpleGraph GraphMinor.Crossing GraphMinor.HP25

/-- The inner vertices allowed by a bridge search: its component, or no vertices for a chord. -/
@[expose] def bridgeInnerVertices {V : Type*} : BridgeData V → List V
  | .comp A => A
  | .chord _ _ => []

/-- The allowed inner vertices of a valid bridge avoid the cycle. -/
theorem validBridgeList_innerVertices_avoid {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {verts D : List V}
    {bridges : List (BridgeData V)} (hB : Crossing.ValidBridgeList G verts D bridges)
    {bd : BridgeData V} (hbd : bd ∈ bridges) :
    ∀ v ∈ bridgeInnerVertices bd, v ∉ D := by
  cases bd with
  | comp A => exact (hB.valid_mem _ hbd).2 A rfl |>.2
  | chord x y => simp [bridgeInnerVertices]

/-- Two distinct attachments of a bridge can be joined through its inner vertices.
This supplies the reachability input of `bridgeAllowedPathProg_exec`. -/
theorem bridge_attachments_search_reachable {V : Type*} {G : SimpleGraph V}
    {S : Set V} {D : List V} {bd : BridgeData V}
    (hB : IsBridge G S D bd.toBridge) {x y : V}
    (hx : IsBridgeAttachment G D bd.toBridge x)
    (hy : IsBridgeAttachment G D bd.toBridge y) (hxy : x ≠ y) :
    ∃ z : V, G.Adj z y ∧ ∃ W : G.Walk x z,
      ∀ v ∈ W.support, v ≠ y ∧ (v = x ∨ v ∈ bridgeInnerVertices bd) := by
  obtain ⟨P, hP, hUses⟩ := exists_isTPath_of_bridge_attachments hB hx hy hxy
  have hrevPath : P.reverse.IsPath := hP.1.reverse
  cases hrev : P.reverse with
  | nil => exact False.elim (hxy rfl)
  | @cons _ z _ hyz W =>
    rw [hrev, Walk.cons_isPath_iff] at hrevPath
    refine ⟨z, hyz.symm, W.reverse, fun v hv => ?_⟩
    have hvW : v ∈ W.support := by simpa using hv
    have hvy : v ≠ y := fun h => hrevPath.2 (h ▸ hvW)
    have hvP : v ∈ P.support := by
      have : v ∈ P.reverse.support := by rw [hrev]; exact List.mem_cons_of_mem _ hvW
      simpa using this
    refine ⟨hvy, ?_⟩
    by_cases hvx : v = x
    · exact Or.inl hvx
    · right
      cases bd with
      | comp A => exact hUses.2 v hvP hvx hvy
      | chord a b =>
        rcases hUses.1 v hvP with h | h
        · exact False.elim (hvx h)
        · exact False.elim (hvy h)

/-- Inner-vertex lists of distinct bridges are disjoint. -/
theorem bridgeInnerVertices_disjoint {V : Type*} {G : SimpleGraph V} {S : Set V}
    {D : List V} {bd₁ bd₂ : BridgeData V}
    (h₁ : IsBridge G S D bd₁.toBridge) (h₂ : IsBridge G S D bd₂.toBridge)
    (hne : bd₁.toBridge ≠ bd₂.toBridge) :
    (bridgeInnerVertices bd₁).Disjoint (bridgeInnerVertices bd₂) := by
  cases bd₁ with
  | chord a b => simp [bridgeInnerVertices]
  | comp A =>
    cases bd₂ with
    | chord a b => simp [bridgeInnerVertices]
    | comp B =>
      have h := IsBridge.disjoint_of_ne h₁ h₂ hne
      exact fun v hvA hvB => Set.disjoint_left.1 h hvA hvB

/-- Two simple paths with four distinct ends on `D` and disjoint inner-vertex lists avoiding
`D` have disjoint supports. -/
theorem bridge_paths_support_disjoint {V : Type*} {G : SimpleGraph V} {D A B : List V}
    {x y z t : V} {Q : G.Walk x y} {R : G.Walk z t}
    (hx : x ∈ D) (hy : y ∈ D) (hz : z ∈ D) (ht : t ∈ D)
    (hxz : x ≠ z) (hxt : x ≠ t) (hyz : y ≠ z) (hyt : y ≠ t)
    (hA : ∀ v ∈ A, v ∉ D) (hB : ∀ v ∈ B, v ∉ D) (hAB : A.Disjoint B)
    (hQ : ∀ v ∈ Q.support, v ≠ x → v ≠ y → v ∈ A)
    (hR : ∀ v ∈ R.support, v ≠ z → v ≠ t → v ∈ B) :
    Q.support.Disjoint R.support := by
  intro v hvQ hvR
  by_cases hvx : v = x
  · subst v
    exact hB x (hR x hvR hxz hxt) hx
  by_cases hvy : v = y
  · subst v
    exact hB y (hR y hvR hyz hyt) hy
  have hvA := hQ v hvQ hvx hvy
  have hvz : v ≠ z := fun h => hA v hvA (h ▸ hz)
  have hvt : v ≠ t := fun h => hA v hvA (h ▸ ht)
  exact hAB hvA (hR v hvR hvz hvt)

/-- Paths inside disjoint bridge interiors yield a crossing when their endpoint indices
interleave. This checks the output of the two searches in Section 5.2. -/
theorem isCrossingPair_of_interleaving_bridge_paths {V : Type*} {G : SimpleGraph V}
    {D A B : List V} (hD : D.Nodup) {i j k l : ℕ}
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hl : l < D.length)
    {Q : G.Walk (D[i]'(by omega)) (D[k]'(by omega))}
    {R : G.Walk (D[j]'(by omega)) (D[l]'hl)}
    (hQpath : Q.IsPath) (hRpath : R.IsPath)
    (hA : ∀ v ∈ A, v ∉ D) (hB : ∀ v ∈ B, v ∉ D) (hAB : A.Disjoint B)
    (hQ : ∀ v ∈ Q.support, v ≠ D[i] → v ≠ D[k] → v ∈ A)
    (hR : ∀ v ∈ R.support, v ≠ D[j] → v ≠ D[l] → v ∈ B) :
    IsCrossingPair G D Q.support R.support := by
  have hi : i < D.length := by omega
  have hj : j < D.length := by omega
  have hk : k < D.length := by omega
  have hne : ∀ {a b : ℕ} (ha : a < D.length) (hb : b < D.length),
      a ≠ b → D[a]'ha ≠ D[b]'hb :=
    fun _ _ hab heq => hab (hD.getElem_inj_iff.mp heq)
  apply Crossing.isCrossingPair_of_isCrossing hD
  refine ⟨⟨i, j, k, l, hij, hjk, hkl, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hl⟩,
    ⟨hQpath, List.getElem_mem hi, List.getElem_mem hk, ?_⟩,
    ⟨hRpath, List.getElem_mem hj, List.getElem_mem hl, ?_⟩, ?_⟩
  · intro v hv hvi hvk
    exact ⟨hA v (hQ v hv hvi hvk), hA v (hQ v hv hvi hvk)⟩
  · intro v hv hvj hvl
    exact ⟨hB v (hR v hv hvj hvl), hB v (hR v hv hvj hvl)⟩
  · exact bridge_paths_support_disjoint (List.getElem_mem hi) (List.getElem_mem hk)
      (List.getElem_mem hj) (List.getElem_mem hl)
      (hne hi hj (by omega)) (hne hi hl (by omega))
      (hne hk hj (by omega)) (hne hk hl (by omega)) hA hB hAB hQ hR

end GraphMinor.Compute
