module

public import GraphMinor.HP25.Lemma41
public import GraphMinor.HP25.Lemma43Case2
public import GraphMinor.HP25.Lemma43
import GraphMinor.HP25.Lemma43Fan
import GraphMinor.HP25.Lemma43ClaimA
import GraphMinor.HP25.Lemma43Path
import GraphMinor.HP25.Lemma43Reroute
import GraphMinor.HP25.Lemma33
import GraphMinor.HP25.Completion
import GraphMinor.HP25.CrossTools
import GraphMinor.HP25.Prop34
import GraphMinor.HP25.Split
import GraphMinor.HP25.SplitTools
import GraphMinor.HP25.CycleEdges

/-!
# Lemma 4.3, second case: `PzCx` is crossless in `H` when `y` sees all of `P`

In the second case of the proof of Lemma 4.3 (`Case2`), the paper applies induction to "a graph $H$
(the orange area above the triangular shapes) containing $PzCx$ as a cycle" (page 15), which needs
`PzCx` crossless in `H = G[𝒞 ∪ P]`. We prove this when `y` is adjacent to every vertex of `P`
(`Case2.not_isCrossed_H`). Then `G` contains the two pieces of the proof of Lemma 4.1: `H` with
frame `PzCx`, and the fan `K = G[P ∪ {y}]` with frame `x y z P⁻¹`, meeting in the induced path `P`.
Claim 4.2 holds on both sides: in `H` it is Claim A (`IsMuMin.claim_A`) with the connectivity of
`𝒞`, and in `K` every vertex of `P` is adjacent to `y`. So the extension of crossings of Lemma 4.1
(`Setting.cross_of_side`, with no new edge) turns a crossing of `PzCx` in `H` into a crossing of
`C` in `G`, which is crossless.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- Adding the edge from a vertex to itself adds nothing. -/
theorem sup_edge_self (x : V) : G ⊔ edge x x = G := by
  ext u v
  simp only [sup_adj, edge_adj]
  constructor
  · rintro (h | ⟨h1 | h1, h2⟩)
    · exact h
    · exact absurd (h1.1.trans h1.2.symm) h2
    · exact absurd (h1.1.trans h1.2.symm) h2
  · exact Or.inl

namespace Case2

variable {S : Set V} {x y z ℓ : V} {L P : List V}

/-- From a vertex `c` of `𝒞` there is a path of `G[𝒞 ∪ P]` to a vertex of `L` whose other
vertices are in `𝒞` and off `L`. -/
theorem reach_L (hc : Case2 G S x y z ℓ L P) {c : V} (hcK : c ∈ compOf G S {v | v ∈ P} ℓ) :
    ∃ l ∈ L, ∃ p : (restrict G (compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P})).Walk c l, p.IsPath ∧
      ∀ w ∈ p.support, w ≠ l → w ∈ compOf G S {v | v ∈ P} ℓ ∧ w ∉ L := by
  classical
  obtain ⟨W⟩ := hcK
  set W' := W.reverse.bypass with hW'
  have hW'K : ∀ w ∈ W'.support, w ∈ compOf G S {v | v ∈ P} ℓ := fun w hw =>
    Reachable.trans ⟨W⟩ (W'.takeUntil w hw).reachable
  obtain ⟨l, hl, p₀, h1, h2, h3⟩ := exists_first_hit {v | v ∈ L} W' hc.mem
  have hp₀K : ∀ w ∈ p₀.support, w ∈ compOf G S {v | v ∈ P} ℓ := fun w hw => hW'K w (h1 w hw)
  have hE : ∀ e ∈ p₀.edges,
      e ∈ (restrict G (compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P})).edgeSet := by
    intro e he
    have hE := p₀.edges_subset_edgeSet he
    induction e using Sym2.ind with
    | _ u v =>
      exact ⟨hE.1, Or.inl (hp₀K u (p₀.fst_mem_support_of_mem_edges he)),
        Or.inl (hp₀K v (p₀.snd_mem_support_of_mem_edges he))⟩
  refine ⟨l, hl, p₀.transfer _ hE, (h3 W.reverse.bypass_isPath).transfer _, fun w hw hwl => ?_⟩
  rw [Walk.support_transfer] at hw
  exact ⟨hp₀K w hw, h2 w hw hwl⟩

/-- **`y` sees `P` gives the gap.** In the second case, if `y` is adjacent to every vertex of `P`,
then `P L` (the paper's `PzCx`) is crossless in `G[𝒞 ∪ P]`. -/
theorem not_isCrossed_H [Finite V] (hc : Case2 G S x y z ℓ L P) (hfan : ∀ t ∈ P, G.Adj y t) :
    ¬ IsCrossed (restrict G (compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P})) (P ++ L) := by
  classical
  intro hcr
  set K := compOf G S {v | v ∈ P} ℓ with hK
  have hnd := hc.cyc.2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  obtain ⟨M, hM⟩ := hc.mu.1.exists_middle (hc.mu.1.two_le_length hc.cyc)
  have hyP : y ∉ P := hc.y_not_mem
  have hyK : y ∉ K := hc.mu.1.y_not_mem hc.max.2.1 hc.cyc hc.mem
  have hLP : ∀ v ∈ L, v ∉ P := fun v hv => hc.mu.1.L_not_mem hc.cyc hv
  have hLK : ∀ v ∈ L, v ∈ K := hc.mu.1.L_mem hc.cyc hc.sub hc.mem
  have hPnd : P.Nodup := hc.mu.1.2.1
  have hmemP : ∀ v, v ∈ P ↔ v = x ∨ v ∈ M ∨ v = z := fun v => by
    rw [hM]; simp
  have hxP : x ∈ P := (hmemP x).mpr (Or.inl rfl)
  have hzP : z ∈ P := (hmemP z).mpr (Or.inr (Or.inr rfl))
  have hxz : x ≠ z := hnd.1.2.1
  -- the frames of the two sides
  have hCH : ∀ w, w ∈ z :: L ++ x :: M.reverse.reverse ↔ w ∈ L ∨ w ∈ P := fun w => by
    rw [hmemP]
    simp only [List.reverse_reverse, List.cons_append, List.mem_cons, List.mem_append]
    tauto
  have hCK : ∀ w, w ∈ x :: [y] ++ z :: M.reverse ↔ w = y ∨ w ∈ P := fun w => by
    rw [hmemP]
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse,
      List.not_mem_nil]
    tauto
  have hPr : P.reverse = z :: M.reverse ++ [x] := by rw [hM]; simp
  have hS : Setting G (K ∪ {v | v ∈ P}) ({v | v ∈ P} ∪ {y}) z x M.reverse L [y]
      (x :: y :: z :: L) 2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the two sides meet in `P`
      ext v
      have : v ∈ z :: M.reverse ++ [x] ↔ v ∈ P := by rw [← hPr, List.mem_reverse]
      simp only [mem_inter_iff, mem_union, mem_singleton_iff, mem_ofPred_eq, this]
      constructor
      · rintro ⟨h1 | h1, h2 | h2⟩
        · exact absurd h2 (hc.K_not_mem h1)
        · exact absurd (h2 ▸ h1) hyK
        · exact h1
        · exact h1
      · exact fun h => ⟨Or.inr h, Or.inl h⟩
    · -- `P` is induced
      intro u hu v hv huv
      rw [← hPr, List.mem_reverse] at hu hv
      rw [← hPr]
      refine IsListEdge.reverse ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
      rcases lt_trichotomy i j with h | rfl | h
      · by_cases h2 : i + 2 ≤ j
        · exact absurd huv (hc.mu.induced hc.ℓ_mem_S hc.ℓ_not_mem h2 hj)
        · have e : j = i + 1 := by omega
          subst e
          exact isListEdge_getElem P i hj
      · exact absurd rfl (G.ne_of_adj huv)
      · by_cases h2 : j + 2 ≤ i
        · exact absurd huv.symm (hc.mu.induced hc.ℓ_mem_S hc.ℓ_not_mem h2 hi)
        · have e : i = j + 1 := by omega
          subst e
          exact (isListEdge_getElem P j hi).symm
    · -- the frame of `H` is a cycle
      have h := hc.isCycleList_H
      rw [show P ++ L = x :: M ++ z :: L by rw [hM]; simp] at h
      have h' := h.rotate (M.length + 1)
      rw [rotate_cons_append_cons] at h'
      rw [List.reverse_reverse]
      exact h'
    · intro v hv
      rcases (hCH v).mp hv with h | h
      · exact Or.inl (hLK v h)
      · exact Or.inr h
    · -- Claim 4.2 in `H`: Claim A and the connectivity of `𝒞`
      intro t ht
      have hin : ∀ w, w ∈ K → w ∉ L → w ∉ {u | u ∈ z :: L ++ x :: M.reverse.reverse} :=
        fun w hwK hwL hw => by
          rcases (hCH w).mp hw with h | h
          · exact hwL h
          · exact hc.K_not_mem hwK h
      rcases ht with ht | ht
      · obtain ⟨l, hl, p, hp, hpK⟩ := hc.reach_L ht
        exact ⟨l, hl, p, hp, fun w hw h1 h2 => hin w (hpK w hw h2).1 (hpK w hw h2).2⟩
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (show t ∈ P from ht)
        obtain ⟨c, hcK, hadj⟩ := hc.mu.claim_A hc.max hc.cyc hc.sub hc.mem i hi
        obtain ⟨l, hl, p, hp, hpK⟩ := hc.reach_L hcK
        have hPi : P[i] ∉ p.support := fun h => by
          by_cases e : P[i] = l
          · exact hLP l hl (e ▸ List.getElem_mem _)
          · exact hc.K_not_mem (hpK _ h e).1 (List.getElem_mem _)
        refine ⟨l, hl, Walk.cons (show (restrict G (K ∪ {v | v ∈ P})).Adj P[i] c from
          ⟨hadj, Or.inr (List.getElem_mem _), Or.inl hcK⟩) p,
          (Walk.cons_isPath_iff _ _).mpr ⟨hp, hPi⟩, fun w hw h1 h2 => ?_⟩
        rw [Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact absurd rfl h1
        · exact hin w (hpK w hw h2).1 (hpK w hw h2).2
    · -- the frame of the fan is a cycle
      have hxyz : (x :: [y] ++ [z]).Nodup := by
        show [x, y, z].Nodup
        simp [hnd.1.1, hxz, hnd.2.1.1]
      have h₁ : IsPathList (restrict G ({v | v ∈ P} ∪ {y})) univ (x :: [y] ++ [z]) := by
        refine ⟨hxyz, ?_, fun _ _ => trivial⟩
        have hxy := hc.cyc.adj_of_isCycleEdge (u := x) (v := y)
          (isCycleEdge_of_isListEdge (x := x) (t := y :: z :: L) ⟨(x, y), by simp, rfl⟩)
        have hyz := hc.cyc.adj_of_isCycleEdge (u := y) (v := z)
          (isCycleEdge_of_isListEdge (x := x) (t := y :: z :: L) ⟨(y, z), by simp, rfl⟩)
        show [x, y, z].IsChain _
        simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
        exact ⟨⟨hxy, Or.inl hxP, Or.inr rfl⟩, ⟨hyz, Or.inr rfl, Or.inl hzP⟩⟩
      have h₂ : IsPathList (restrict G ({v | v ∈ P} ∪ {y})) univ (z :: M.reverse ++ [x]) := by
        rw [← hPr]
        refine ⟨List.nodup_reverse.mpr hPnd, ?_, fun _ _ => trivial⟩
        exact List.isChain_reverse.mpr ((isChain_restrict hc.mu.1.1
          (X := {v | v ∈ P} ∪ {y}) fun v hv => Or.inl hv).imp fun _ _ h => h.symm)
      exact isCycleList_of_two_paths h₁ h₂ (fun v hv hvM => by
        rw [List.mem_singleton] at hv
        subst hv
        exact hyP ((hmemP v).mpr (Or.inr (Or.inl (List.mem_reverse.mp hvM))))) hxz
        (Or.inl (by simp))
    · intro v hv
      rcases (hCK v).mp hv with h | h
      · exact Or.inr h
      · exact Or.inl h
    · -- Claim 4.2 in the fan: every vertex of `P` is adjacent to `y`
      intro t ht
      rcases ht with ht | ht
      · have hadj : (restrict G ({v | v ∈ P} ∪ {y})).Adj t y :=
          ⟨(hfan t ht).symm, Or.inl ht, Or.inr rfl⟩
        refine ⟨y, by simp, hadj.toWalk, Walk.IsPath.of_adj hadj, fun w hw h1 h2 => ?_⟩
        rw [support_toWalk, List.mem_cons, List.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact absurd rfl h1
        · exact absurd rfl h2
      · rw [mem_singleton_iff] at ht
        subst ht
        exact ⟨t, by simp, Walk.nil, Walk.IsPath.nil, fun w hw h1 _ => by
          simp at hw
          exact absurd hw h1⟩
    · simp [List.rotate_cons_succ]
    · exact List.ne_nil_of_mem hc.mem
    · simp
  have hcr' : IsCrossed (restrict G (K ∪ {v | v ∈ P}) ⊔ edge x x)
      (z :: L ++ x :: M.reverse.reverse) := by
    rw [List.reverse_reverse]
    refine IsCrossed.of_rotate (L.length + 1) ?_
    rw [rotate_cons_append_cons]
    have e : P ++ L = x :: M ++ z :: L := by rw [hM]; simp
    rw [← e]
    exact IsCrossed.mono hcr le_sup_left
  have := hS.cross_of_side (Or.inr hxP) (Or.inr hxP) hcr'
  rw [sup_edge_self] at this
  exact hc.max.2.1 this

end Case2

end GraphMinor.HP25

namespace GraphMinor.HP25

/-- **`y` sees all of `P`.** In the second case of the proof of Lemma 4.3, `y` is adjacent to every
vertex of the `μ`-minimal path `P`. No proof is known. A computer search on small graphs found no
counterexample. -/
@[expose] public def Lemma43Fan (V : Type*) : Prop :=
  ∀ (G : SimpleGraph V) (S : Set V) (x y z ℓ : V) (L P : List V), Case2 G S x y z ℓ L P →
    ∀ t ∈ P, G.Adj y t

/-- `Lemma43Fan` gives the gap of Lemma 4.3 (`Case2.not_isCrossed_H`). -/
public theorem lemma43Gap_of_fan {V : Type*} [Finite V] (h : Lemma43Fan V) : Lemma43Gap V :=
  fun G S x y z ℓ L P hc => hc.not_isCrossed_H (h G S x y z ℓ L P hc)

end GraphMinor.HP25
