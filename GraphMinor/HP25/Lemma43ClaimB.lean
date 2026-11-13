module

public import GraphMinor.HP25.Lemma43ClaimA
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma43Reroute
import GraphMinor.HP25.Prop34

/-!
# Lemma 4.3, second case: the other components of `G - P - y`

Humeau and Pous, proof of Lemma 4.3 (page 15): "components of $G-P-y$ that are incident to $y$ are
incident to at most two vertices of $P$ and those are consecutive in $P$. Indeed if such a
component could join two non-consecutive vertices $s$ and $t$ of $P$ in a $C\cup P$-path $Q$ not
intersecting $\mathcal{C}_C^P$, then $PsQtP$ would give a better path than $P$ with regard to the
measure $\mu$."

We prove this for every component of `G - P - y` other than the one of `C - {x, y, z}`
(`Case2.claim_B`), whether or not it touches `y`: the argument does not use `y`. The vertex of `P`
between `s` and `t` has a neighbour in `𝒞_C^P` by Claim A, so `IsMuMin.no_detour` applies.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- The setting of the second case of the proof of Lemma 4.3: `G` is maximally crossless on `S`
for the cycle `C = x y z L`, `ℓ` is a vertex of `L = C - {x, y, z}`, and `P` is a `μ`-minimal
path from `x` to `z` inner disjoint from `C`. -/
structure Case2 (G : SimpleGraph V) (S : Set V) (x y z ℓ : V) (L P : List V) : Prop where
  max : IsMaxCrosslessOn G S (x :: y :: z :: L)
  cyc : IsCycleList G (x :: y :: z :: L)
  sub : ∀ v ∈ x :: y :: z :: L, v ∈ S
  mem : ℓ ∈ L
  mu : IsMuMin G S (x :: y :: z :: L) x z ℓ P

namespace Case2

variable {S : Set V} {x y z ℓ : V} {L P : List V}

theorem restrict_mono {A B : Set V} (h : A ⊆ B) : restrict G A ≤ restrict G B :=
  fun _ _ hab => ⟨hab.1, h hab.2.1, h hab.2.2⟩

theorem ℓ_not_mem (hc : Case2 G S x y z ℓ L P) : ℓ ∉ P := hc.mu.1.L_not_mem hc.cyc hc.mem

theorem ℓ_mem_S (hc : Case2 G S x y z ℓ L P) : ℓ ∈ S := hc.sub ℓ (by simp [hc.mem])

theorem P_sub (hc : Case2 G S x y z ℓ L P) : ∀ v ∈ P, v ∈ S :=
  mem_of_isChain hc.max.1 hc.mu.1.1 (hc.mu.1.two_le_length hc.cyc)

/-- The component `𝒞_C^P` misses `P`. -/
theorem K_not_mem (hc : Case2 G S x y z ℓ L P) {k : V}
    (hk : k ∈ compOf G S {v | v ∈ P} ℓ) : k ∉ P :=
  (compOf_subset (G := G) (Y := {v | v ∈ P}) ⟨hc.ℓ_mem_S, hc.ℓ_not_mem⟩ hk).2

theorem K_mem_S (hc : Case2 G S x y z ℓ L P) {k : V}
    (hk : k ∈ compOf G S {v | v ∈ P} ℓ) : k ∈ S :=
  (compOf_subset (G := G) (Y := {v | v ∈ P}) ⟨hc.ℓ_mem_S, hc.ℓ_not_mem⟩ hk).1

/-- A component of `G - P - y` that does not hold `ℓ` misses `𝒞_C^P`. -/
theorem Z_not_K {v w : V}
    (hvK : v ∉ compOf G S {v | v ∈ P} ℓ) (hw : w ∈ compOf G S {u | u ∈ P ∨ u = y} v) :
    w ∉ compOf G S {v | v ∈ P} ℓ := fun hwK =>
  hvK (Reachable.trans hwK (Reachable.mono
    (restrict_mono fun _ hu => ⟨hu.1, fun h' => hu.2 (Or.inl h')⟩) (Reachable.symm hw)))

/-- **Claim B** (page 15). Two vertices `u`, `u'` of a component of `G - P - y` other than the one
of `ℓ` have no neighbours `P[j]`, `P[j']` on `P` with `j + 1 < j'`. Otherwise the path
`P[j] u … u' P[j']` through the component replaces `P[j+1]`, which has a neighbour in `𝒞_C^P` by
Claim A, and `IsMuMin.no_detour` gives a contradiction. -/
theorem claim_B [Finite V] (hc : Case2 G S x y z ℓ L P) {v : V}
    (hv : v ∈ S \ {u | u ∈ P ∨ u = y}) (hvK : v ∉ compOf G S {v | v ∈ P} ℓ) {u u' : V}
    (hu : u ∈ compOf G S {u | u ∈ P ∨ u = y} v) (hu' : u' ∈ compOf G S {u | u ∈ P ∨ u = y} v)
    {j j' : ℕ} (hj : j < P.length) (hj' : j' < P.length) (ha : G.Adj u P[j])
    (ha' : G.Adj u' P[j']) : j' ≤ j + 1 := by
  classical
  by_contra hlt
  push Not at hlt
  have hnd := hc.mu.1.2.1
  have hZ := compOf_subset (G := G) hv
  obtain ⟨W⟩ : (restrict G (S \ {u | u ∈ P ∨ u = y})).Reachable u u' := hu.symm.trans hu'
  set Wp := W.bypass.mapLe (restrict_le G _) with hWp
  have hWpath : Wp.IsPath := (Walk.isPath_mapLe _).mpr W.bypass_isPath
  have hWs : ∀ w ∈ Wp.support, w ∈ compOf G S {u | u ∈ P ∨ u = y} v := by
    intro w hw
    rw [hWp, Walk.support_mapLe_eq_support] at hw
    have hw' := W.support_bypass_subset_support hw
    exact hu.trans (W.takeUntil w hw').reachable
  have hWY : ∀ w ∈ Wp.support, w ∉ P := fun w hw hwP => (hZ (hWs w hw)).2 (Or.inl hwP)
  have hjj : P[j] ≠ P[j'] := fun e => by
    have := hnd.getElem_inj_iff.mp e
    omega
  have hpath : (Walk.cons ha.symm (Wp.concat ha')).IsPath := by
    refine (hWpath.concat (hWY _ · (List.getElem_mem _)) ha').cons ?_
    rw [Walk.support_concat, List.mem_append, List.mem_singleton, not_or]
    exact ⟨(hWY _ · (List.getElem_mem _)), hjj⟩
  have hmem : ∀ w ∈ (Walk.cons ha.symm (Wp.concat ha')).support,
      w = P[j] ∨ w ∈ Wp.support ∨ w = P[j'] := by
    intro w hw
    simpa [Walk.support_concat] using hw
  have hPj : ∀ {i} (hi : i < P.length), P[i] ∉ compOf G S {v | v ∈ P} ℓ := fun hi hk =>
    hc.K_not_mem hk (List.getElem_mem hi)
  refine hc.mu.no_detour hc.ℓ_mem_S hc.ℓ_not_mem (p₂ := j) (p₄ := j') (m := j + 1) (by omega)
    hlt hj' (Y₀ := (Walk.cons ha.symm (Wp.concat ha')).support) (Walk.isChain_adj_support _)
    hpath.support_nodup (Walk.support_head? _) (Walk.support_getLast? _) ?_ ?_ ?_ ?_
    (hc.P_sub _ (List.getElem_mem _))
    (hc.mu.claim_A hc.max hc.cyc hc.sub hc.mem (j + 1) (by omega))
  · intro w hw hwP
    rcases hmem w hw with rfl | hw | rfl
    · exact Or.inl rfl
    · exact absurd hwP (hWY w hw)
    · exact Or.inr rfl
  · intro w hw hwC
    rcases hmem w hw with rfl | hw | rfl
    · exact List.getElem_mem _
    · exfalso
      have hwZ := hZ (hWs w hw)
      simp only [List.mem_cons] at hwC
      rcases hwC with rfl | rfl | rfl | hwL
      · exact hwZ.2 (Or.inl hc.mu.1.x_mem)
      · exact hwZ.2 (Or.inr rfl)
      · exact hwZ.2 (Or.inl hc.mu.1.z_mem)
      · exact Z_not_K hvK (hWs w hw) (hc.mu.1.L_mem hc.cyc hc.sub hc.mem w hwL)
    · exact List.getElem_mem _
  · intro w hw
    rcases hmem w hw with rfl | hw | rfl
    · exact hPj hj
    · exact Z_not_K hvK (hWs w hw)
    · exact hPj hj'
  · intro hm
    rcases hmem _ hm with e | hw | e
    · have := hnd.getElem_inj_iff.mp e
      omega
    · exact hWY _ hw (List.getElem_mem _)
    · have := hnd.getElem_inj_iff.mp e
      omega

end Case2

end GraphMinor.HP25
