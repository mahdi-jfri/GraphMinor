module

public import GraphMinor.HP25.Defs
public import GraphMinor.HP25.Web
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import GraphMinor.HP25.Lemma43Tools
public import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Prop34
import GraphMinor.HP25.CrossTools

/-!
# Lemma 4.3, second case: the path `P` and the measure `μ`

Humeau and Pous, proof of Lemma 4.3 (page 14), case 2: "Take consecutive vertices $x,y,z$ on $C$
with an $x$-$z$ path $P$ inner disjoint from $C$. For such a path $P$ we write $\mathcal{C}_C^P$ for
the component of $C-\{x,y,z\}$ in $G-P$. We assume that $P$ is minimal with regard to the measure
$$\mu(P)=(|G|-|\mathcal{C}_C^P|,|P|)$$ ... In particular, $P$ is induced."

Here `G` is a graph on the finite vertex set `S`, `C = x y z L`, and `ℓ` is the first vertex of `L`.

* `compOf G S Y ℓ`: the vertices that `ℓ` reaches in `G` on `S` minus `Y`. For `Y` the vertex set of
  `P`, this is `𝒞_C^P`: `L` is connected in `G - P` (`IsXZPath.L_mem`), so the component of
  `C - {x, y, z}` is the component of `ℓ`.
* `IsXZPath G C x z P`: `P` is a path list from `x` to `z` whose only vertices on `C` are its ends.
* `IsMuMin G S C x z ℓ P`: `P` minimises `μ`, in the lexicographic order: no other such path has a
  larger component, or the same component size and fewer vertices.
* `exists_isMuMin`: such a `P` exists when some `x`-`z` path inner disjoint from `C` exists.
* `IsMuMin.not_better`: a path with a strictly larger component containing the old one, or the same
  component and fewer vertices, contradicts minimality. All later steps of case 2 use it.
* `IsMuMin.induced`: "In particular, $P$ is induced."
* `IsXZPath.y_not_mem`: `y` is not in `𝒞_C^P`, since a path from `y` to `L` avoiding `P` would form a
  crossing with `P`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- The vertices that `ℓ` reaches in the graph `G` on `S` minus `Y`. -/
@[expose] def compOf (G : SimpleGraph V) (S Y : Set V) (ℓ : V) : Set V :=
  {v | (restrict G (S \ Y)).Reachable ℓ v}

/-- `P` is a path (as a list of vertices) from `x` to `z` whose only vertices on `C` are `x` and
`z`: "an $x$-$z$ path $P$ inner disjoint from $C$" (page 14). -/
@[expose] def IsXZPath (G : SimpleGraph V) (C : List V) (x z : V) (P : List V) : Prop :=
  P.IsChain G.Adj ∧ P.Nodup ∧ P.head? = some x ∧ P.getLast? = some z ∧
    ∀ v ∈ P, v ∈ C → v = x ∨ v = z

/-- `P` is minimal for the measure `μ` (page 14): "We assume that $P$ is minimal with regard to the
measure $$\mu(P)=(|G|-|\mathcal{C}_C^P|,|P|)$$ where the order on $\mathbb{N}\times\mathbb{N}$ is the
lexicographic product of the usual order $<$." Here `𝒞_C^P` is `compOf G S P ℓ`, for `ℓ` a vertex
of `C - {x, y, z}`. -/
@[expose] def IsMuMin (G : SimpleGraph V) (S : Set V) (C : List V) (x z ℓ : V) (P : List V) :
    Prop :=
  IsXZPath G C x z P ∧ ∀ P', IsXZPath G C x z P' →
    (compOf G S {v | v ∈ P'} ℓ).ncard ≤ (compOf G S {v | v ∈ P} ℓ).ncard ∧
    ((compOf G S {v | v ∈ P'} ℓ).ncard = (compOf G S {v | v ∈ P} ℓ).ncard →
      P.length ≤ P'.length)

/-! ### Components -/

section Comp

variable {S Y Y' : Set V} {ℓ : V}

theorem mem_compOf_self : ℓ ∈ compOf G S Y ℓ := Reachable.refl _

/-- The component lies in `S \ Y` when `ℓ` does. -/
theorem compOf_subset (hℓ : ℓ ∈ S \ Y) : compOf G S Y ℓ ⊆ S \ Y := by
  rintro v ⟨W⟩
  by_cases hv : v = ℓ
  · exact hv ▸ hℓ
  · exact mem_of_mem_support_restrict W W.end_mem_support hv

/-- The component is closed under neighbours in `S \ Y`. -/
theorem compOf_adj (hℓ : ℓ ∈ S \ Y) {u v : V} (hu : u ∈ compOf G S Y ℓ) (hv : v ∈ S \ Y)
    (huv : G.Adj u v) : v ∈ compOf G S Y ℓ :=
  Reachable.trans hu (Adj.reachable ⟨huv, compOf_subset hℓ hu, hv⟩)

/-- The vertices of a walk of `G` on `S \ Y` from the component lie in the component. -/
theorem compOf_walk (hℓ : ℓ ∈ S \ Y) :
    ∀ {u v : V} (W : G.Walk u v), u ∈ compOf G S Y ℓ → (∀ w ∈ W.support, w ∈ S \ Y) →
      ∀ w ∈ W.support, w ∈ compOf G S Y ℓ
  | _, _, .nil, hu, _, w, hw => by simp at hw; exact hw ▸ hu
  | _, _, .cons h W, hu, hW, w, hw => by
    rw [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hu
    · exact compOf_walk hℓ W (compOf_adj hℓ hu (hW _ (by simp)) h)
        (fun w hw => hW w (by simp [hw])) w hw

private theorem compOf_mono_aux (h : ∀ v ∈ compOf G S Y ℓ, v ∉ Y') :
    ∀ {u : V} (_ : (restrict G (S \ Y)).Walk u ℓ), (restrict G (S \ Y')).Reachable u ℓ
  | _, .nil => Reachable.refl _
  | u, .cons (v := u') huu W => by
    have hu' : u' ∈ compOf G S Y ℓ := ⟨W.reverse⟩
    have hu : u ∈ compOf G S Y ℓ := ⟨(Walk.cons huu W).reverse⟩
    exact (Adj.reachable (G := restrict G (S \ Y')) ⟨huu.1, ⟨huu.2.1.1, h u hu⟩,
      ⟨huu.2.2.1, h u' hu'⟩⟩).trans
      (compOf_mono_aux h W)

/-- **The component grows when no vertex of it is removed.** If no vertex of the component of `ℓ`
in `S \ Y` lies in `Y'`, the component of `ℓ` in `S \ Y'` contains it. -/
theorem compOf_mono (h : ∀ v ∈ compOf G S Y ℓ, v ∉ Y') :
    compOf G S Y ℓ ⊆ compOf G S Y' ℓ := by
  rintro v ⟨W⟩
  exact (compOf_mono_aux h W.reverse).symm

end Comp

/-! ### Paths from `x` to `z` -/

section Paths

variable {C : List V} {x z : V} {P : List V}

theorem IsXZPath.ne_nil (h : IsXZPath G C x z P) : P ≠ [] := by
  rintro rfl
  exact absurd h.2.2.1 (by simp)

theorem IsXZPath.x_mem (h : IsXZPath G C x z P) : x ∈ P := List.mem_of_mem_head? h.2.2.1

theorem IsXZPath.z_mem (h : IsXZPath G C x z P) : z ∈ P := List.mem_of_mem_getLast? h.2.2.2.1

/-- **The minimal path exists.** If some `x`-`z` path is inner disjoint from `C`, one of them is
minimal for `μ`. -/
theorem exists_isMuMin [Finite V] (S : Set V) (ℓ : V) (h : ∃ P, IsXZPath G C x z P) :
    ∃ P, IsMuMin G S C x z ℓ P := by
  let f : List V → ℕ ×ₗ ℕ := fun P =>
    toLex (Nat.card V - (compOf G S {v | v ∈ P} ℓ).ncard, P.length)
  obtain ⟨P, hP, hmin⟩ := (InvImage.wf f wellFounded_lt).has_min {P | IsXZPath G C x z P} h
  refine ⟨P, hP, fun P' hP' => ?_⟩
  have hn := hmin P' hP'
  simp only [InvImage, f, Prod.Lex.toLex_lt_toLex, not_or, not_and, not_lt] at hn
  have h1 := Set.ncard_le_card (compOf G S {v | v ∈ P} ℓ)
  have h2 := Set.ncard_le_card (compOf G S {v | v ∈ P'} ℓ)
  refine ⟨by omega, fun he => hn.2 (by omega)⟩

/-- **Minimality used.** A path whose component contains the old one, and either has a further
vertex or the same vertices and fewer path vertices, contradicts the minimality of `P`. -/
theorem IsMuMin.not_better [Finite V] {S : Set V} {ℓ : V} (h : IsMuMin G S C x z ℓ P)
    {P' : List V} (hP' : IsXZPath G C x z P')
    (hsub : compOf G S {v | v ∈ P} ℓ ⊆ compOf G S {v | v ∈ P'} ℓ)
    (hbetter : (∃ v ∈ compOf G S {v | v ∈ P'} ℓ, v ∉ compOf G S {v | v ∈ P} ℓ) ∨
      P'.length < P.length) : False := by
  obtain ⟨h1, h2⟩ := h.2 P' hP'
  rcases hbetter with ⟨v, hv, hv'⟩ | hlen
  · have := Set.ncard_lt_ncard (⟨hsub, fun h' => hv' (h' hv)⟩ :
      compOf G S {v | v ∈ P} ℓ ⊂ compOf G S {v | v ∈ P'} ℓ) (Set.toFinite _)
    omega
  · have := h2 (le_antisymm h1 (Set.ncard_le_ncard hsub (Set.toFinite _)))
    omega

/-- The list of vertices of a walk starts at its start. -/
theorem Walk.support_head? {u v : V} (p : G.Walk u v) : p.support.head? = some u := by
  rw [← Walk.cons_tail_support]; rfl

/-- The list of vertices of a walk ends at its end. -/
theorem Walk.support_getLast? {u v : V} (p : G.Walk u v) : p.support.getLast? = some v := by
  rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]

/-- "In particular, $P$ is induced": a chord `P[i] P[j]` would shortcut `P` without removing a
vertex of the component, and make it shorter. -/
theorem IsMuMin.induced [Finite V] {S : Set V} {ℓ : V} (h : IsMuMin G S C x z ℓ P) (hℓ : ℓ ∈ S)
    (hℓP : ℓ ∉ P) {i j : ℕ} (hij : i + 2 ≤ j) (hj : j < P.length) :
    ¬ G.Adj (P[i]'(by omega)) P[j] := by
  intro hadj
  obtain ⟨hch, hnd, hh, hl, hC⟩ := h.1
  have hne : P[i]'(by omega) ≠ P[j] := fun he => by
    have := (hnd.getElem_inj_iff).mp he
    omega
  obtain ⟨c, nd, hh', hl', hmem⟩ := splice (Y₀ := [P[i]'(by omega), P[j]]) hch hnd
    (p₂ := i) (p₄ := j) (by omega) hj (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _)
    (by simp [hadj]) (by simp [hne]) rfl rfl (fun w hw _ => by simpa using hw)
  have hsub : ∀ w ∈ P.take i ++ [P[i]'(by omega), P[j]] ++ P.drop (j + 1), w ∈ P := by
    intro w hw
    rcases hmem w hw with hw | ⟨q, hq, rfl, -⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> exact List.getElem_mem _
    · exact List.getElem_mem _
  have hP' : IsXZPath G C x z (P.take i ++ [P[i]'(by omega), P[j]] ++ P.drop (j + 1)) :=
    ⟨c, nd, hh'.trans hh, hl'.trans hl, fun v hv hvC => hC v (hsub v hv) hvC⟩
  refine h.not_better hP'
    (compOf_mono fun v hv hvP => ?_) (Or.inr (by simp; omega))
  have := compOf_subset (G := G) (Y := {v | v ∈ P}) ⟨hℓ, hℓP⟩ hv
  exact this.2 (hsub v hvP)

/-- **No detour around a vertex with a neighbour in the component.** Replace the part of `P`
strictly between `P[p₂]` and `P[p₄]` by a path `Y₀` that meets `P` only at its ends, misses the
component `𝒞_C^P`, and meets `C` only on `P`. If a removed vertex `P[m]` has a neighbour in
`𝒞_C^P`, the new path has a larger component (the old one and `P[m]`), against minimality. This is
the step "$P$ can be replaced by $PsQtP$ giving a path with lower measure $\mu$" (page 15). -/
theorem IsMuMin.no_detour [Finite V] {S : Set V} {ℓ : V} (h : IsMuMin G S C x z ℓ P)
    (hℓ : ℓ ∈ S) (hℓP : ℓ ∉ P) {p₂ p₄ m : ℕ} (h2m : p₂ < m) (hm4 : m < p₄)
    (h4 : p₄ < P.length) {Y₀ : List V} (hY : Y₀.IsChain G.Adj) (hYnd : Y₀.Nodup)
    (hYh : Y₀.head? = some (P[p₂]'(by omega))) (hYl : Y₀.getLast? = some P[p₄])
    (hYP : ∀ w ∈ Y₀, w ∈ P → w = P[p₂]'(by omega) ∨ w = P[p₄])
    (hYC : ∀ w ∈ Y₀, w ∈ C → w ∈ P) (hYK : ∀ w ∈ Y₀, w ∉ compOf G S {v | v ∈ P} ℓ)
    (hmY : P[m]'(by omega) ∉ Y₀) (hmS : P[m]'(by omega) ∈ S)
    (hgood : ∃ c ∈ compOf G S {v | v ∈ P} ℓ, G.Adj (P[m]'(by omega)) c) : False := by
  obtain ⟨hch, hnd, hh, hl, hC⟩ := h.1
  obtain ⟨c, nd, hh', hl', hmem⟩ := splice hch hnd (p₂ := p₂) (p₄ := p₄) (by omega) h4
    (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _) hY hYnd hYh hYl hYP
  set P' := P.take p₂ ++ Y₀ ++ P.drop (p₄ + 1) with hP'
  have hP'P : ∀ w ∈ P', w ∈ Y₀ ∨ w ∈ P := fun w hw => by
    rcases hmem w hw with hw | ⟨q, hq, rfl, -⟩
    · exact Or.inl hw
    · exact Or.inr (List.getElem_mem _)
  have hXZ : IsXZPath G C x z P' := ⟨c, nd, hh'.trans hh, hl'.trans hl, fun v hv hvC => by
    rcases hP'P v hv with hv | hv
    · exact hC v (hYC v hv hvC) hvC
    · exact hC v hv hvC⟩
  have hKP : ∀ k ∈ compOf G S {v | v ∈ P} ℓ, k ∉ P := fun k hk =>
    (compOf_subset (G := G) (Y := {v | v ∈ P}) ⟨hℓ, hℓP⟩ hk).2
  have hsub : compOf G S {v | v ∈ P} ℓ ⊆ compOf G S {v | v ∈ P'} ℓ :=
    compOf_mono fun k hk hkP' => by
      rcases hP'P k hkP' with hk' | hk'
      · exact hYK k hk' hk
      · exact hKP k hk hk'
  have hmP' : P[m]'(by omega) ∉ P' := by
    intro hm
    rcases hmem _ hm with hm | ⟨q, hq, he, hlt⟩
    · exact hmY hm
    · have := (hnd.getElem_inj_iff).mp he
      omega
  have hℓP' : ℓ ∉ P' := fun h' => by
    rcases hP'P ℓ h' with h1 | h1
    · exact hYK ℓ h1 mem_compOf_self
    · exact hℓP h1
  obtain ⟨c₀, hc₀, hadj⟩ := hgood
  have hmK' : P[m]'(by omega) ∈ compOf G S {v | v ∈ P'} ℓ :=
    compOf_adj ⟨hℓ, hℓP'⟩ (hsub hc₀) ⟨hmS, hmP'⟩ hadj.symm
  exact h.not_better hXZ hsub (Or.inl ⟨_, hmK', fun h' => hKP _ h' (List.getElem_mem _)⟩)

end Paths

/-! ### The frame `x y z L` -/

section Frame

variable {S : Set V} {x y z : V} {L P : List V}

/-- The vertices of `L` lie in `G - P`. -/
theorem IsXZPath.L_not_mem (hC : IsCycleList G (x :: y :: z :: L))
    (hP : IsXZPath G (x :: y :: z :: L) x z P) {v : V} (hv : v ∈ L) : v ∉ P := by
  intro hvP
  have hnd := hC.2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  rcases hP.2.2.2.2 v hvP (by simp [hv]) with rfl | rfl
  · exact hnd.1.2.2 hv
  · exact hnd.2.2.1 hv

/-- `L` is connected in `G - P`, so it lies in the component of any of its vertices. -/
theorem IsXZPath.L_mem (hC : IsCycleList G (x :: y :: z :: L))
    (hCS : ∀ v ∈ x :: y :: z :: L, v ∈ S) (hP : IsXZPath G (x :: y :: z :: L) x z P) {ℓ : V}
    (hℓ : ℓ ∈ L) : ∀ v ∈ L, v ∈ compOf G S {v | v ∈ P} ℓ := by
  have hch := (hC.isPathList (R := univ) fun _ _ => trivial).2.1
  have hL : L.IsChain G.Adj := hch.tail.tail.tail
  intro v hv
  exact chain_reach (X := S \ {v | v ∈ P}) hL (fun w hw => ⟨hCS w (by simp [hw]), hP.L_not_mem hC hw⟩) ℓ hℓ v hv

/-- `y` is not in the component `𝒞_C^P`: a path from `y` to `L` avoiding `P` would cross `P`. -/
theorem IsXZPath.y_not_mem (hnc : ¬ IsCrossed G (x :: y :: z :: L))
    (hC : IsCycleList G (x :: y :: z :: L)) (hP : IsXZPath G (x :: y :: z :: L) x z P) {ℓ : V}
    (hℓ : ℓ ∈ L) : y ∉ compOf G S {v | v ∈ P} ℓ := by
  rintro ⟨W⟩
  have hnd := hC.2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  have hyP : y ∉ P := by
    intro hyP
    rcases hP.2.2.2.2 y hyP (by simp) with h | h
    · exact hnd.1.1 h.symm
    · exact hnd.2.1.1 h
  have hW : ∀ v ∈ W.reverse.support, v ∈ {v | v ∈ x :: y :: z :: L} →
      v ∈ ({y} : Set V) ∨ v ∈ {v | v ∈ L} := by
    intro v hv hvC
    by_cases hvy : v = y
    · exact Or.inl hvy
    · have hvS := mem_of_mem_support_restrict W.reverse hv hvy
      have hvP : v ∉ P := hvS.2
      simp only [mem_ofPred_eq, List.mem_cons] at hvC
      rcases hvC with rfl | rfl | rfl | hvL
      · exact absurd hP.x_mem hvP
      · exact absurd rfl hvy
      · exact absurd hP.z_mem hvP
      · exact Or.inr hvL
  obtain ⟨a, ha, b, hb, hcon⟩ := exists_connected_of_walk (G := restrict G (S \ {v | v ∈ P}))
    W.reverse hℓ hW y rfl Walk.nil (fun v hv h1 => by simp at hv; exact absurd hv h1)
  rw [mem_singleton_iff] at ha
  subst a
  obtain ⟨b', hb', p, hp, hin⟩ := hcon
  rw [mem_singleton_iff] at hb'
  subst b'
  refine hnc (isCrossed_of_lists (T := x :: y :: z :: L) (k := 0) (L₁ := [y]) (L₂ := L)
    (by simp) (List.mem_singleton_self y) hb hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2
    ((p.isChain_adj_support).imp fun _ _ h => h.1) hp.support_nodup (Walk.support_head? p)
    (Walk.support_getLast? p) (fun w hw hwC => ?_) ?_)
  · by_contra hne
    push Not at hne
    exact hin w hw hne.1 hne.2 hwC
  · intro w hwP hwp
    by_cases hwy : w = y
    · exact hyP (hwy ▸ hwP)
    · exact (mem_of_mem_support_restrict p hwp hwy).2 hwP

end Frame

end GraphMinor.HP25
