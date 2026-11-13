module

public import GraphMinor.HP25.Lemma43Fan
public import GraphMinor.HP25.Alternate
import GraphMinor.HP25.Lemma43Reroute
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma43Case1
import GraphMinor.HP25.CrossTools
import GraphMinor.HP25.Prop31
import GraphMinor.HP25.Prop34
import GraphMinor.HP25.Split

/-!
# Lemma 4.3, second case

Humeau and Pous, proof of Lemma 4.3 (page 15): "In other words, $G$ is the path composition along
$P$ of an edge subgraph of a web (made of the green triangular shapes and whose rib is a fan graph)
with frame $zyxP$ with a graph $H$ (the orange area above the triangular shapes) containing $PzCx$
as a cycle. It is easily proved that $PzCx$ is crossed in any edge extension of $H$, hence $H$ is a
web with frame $PzCx$ by induction."

Write `𝒞` for the component `𝒞_C^P` and `H = G[𝒞 ∪ P]`. We do not show that `H` itself is
maximally `PzCx`-crossless. Instead we take a maximal crossless completion `W₂` of `H` on `𝒞 ∪ P`
(`exists_maxCrosslessOn`), a web by induction, and show that `P` stays induced in `W₂`
(`Case2.no_chord`): a chord `P[i] P[j]` with `i + 2 ≤ j` would cross the path from `P[i+1]`
through `𝒞` to `L` (Claim A). With the fan `W₁` on the other side (`Case2.fan_side`),
`IsMaxCrosslessOn.eq_sup_of_pieces` (Proposition 3.1 and maximality) gives that `G = W₁ ∪ W₂` is
a web with frame `C`.

The completion needs `PzCx` to be crossless in `H`. The paper does not say why. Here
`Case2.isWebOn` takes it as the hypothesis `hgap`, and `HP25/Gap43.lean` proves it (`Case2.gap`);
`lemma_4_3_on` combines the two.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- A chain of `G` whose entries lie in `X` is a chain of `G[X]`. -/
theorem isChain_restrict {X : Set V} : ∀ {l : List V}, l.IsChain G.Adj → (∀ v ∈ l, v ∈ X) →
    l.IsChain (restrict G X).Adj
  | [], _, _ => List.IsChain.nil
  | [_], _, _ => List.isChain_singleton _
  | a :: b :: t, h, hX => by
    rw [List.isChain_cons_cons] at h ⊢
    exact ⟨⟨h.1, hX a (by simp), hX b (by simp)⟩,
      isChain_restrict h.2 fun v hv => hX v (List.mem_cons_of_mem _ hv)⟩

/-- In the cycle `P L`, the ends of a chord `P[i] P[j]` of `P` alternate with `P[i+1]` and any
vertex of `L`. -/
theorem alternate_chord {P L : List V} {i j : ℕ} (hij : i + 2 ≤ j) (hj : j < P.length) {l : V}
    (hl : l ∈ L) : Alternate (P ++ L) (P[i]'(by omega)) P[j] (P[i + 1]'(by omega)) l := by
  refine ⟨i, (P.drop (i + 1)).take (j - i - 1), P.drop (j + 1) ++ L ++ P.take i, ?_, ?_, by simp [hl]⟩
  · rw [List.rotate_eq_drop_append_take (by simp; omega),
      List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by omega),
      List.drop_eq_getElem_cons (by omega)]
    have e : P.drop (i + 1) = (P.drop (i + 1)).take (j - i - 1) ++ P[j] :: P.drop (j + 1) := by
      conv_lhs => rw [← List.take_append_drop (j - i - 1) (P.drop (i + 1))]
      rw [List.drop_drop, show i + 1 + (j - i - 1) = j by omega, List.drop_eq_getElem_cons hj]
    conv_lhs => rw [e]
    simp only [List.cons_append, List.append_assoc]
  · have h0 : 0 < ((P.drop (i + 1)).take (j - i - 1)).length := by simp; omega
    have := List.getElem_mem h0
    simpa using this

/-- The ends of a path with at least two vertices. -/
theorem IsXZPath.exists_middle {C : List V} {x z : V} {P : List V} (hP : IsXZPath G C x z P)
    (h2 : 2 ≤ P.length) : ∃ M, P = x :: M ++ [z] := by
  match P, h2, hP with
  | a :: b :: R, _, hP =>
    have hh := hP.2.2.1
    have hl := hP.2.2.2.1
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    refine ⟨(b :: R).dropLast, ?_⟩
    have hz : (b :: R).getLast (by simp) = z := by
      rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (by simp)] at hl
      exact Option.some.inj hl
    rw [← hz, List.cons_append, List.dropLast_append_getLast]

/-- A web with a rotated frame. -/
theorem IsWebOn.of_rotate {S : Set V} {C : List V} {k : ℕ} (h : IsWebOn G S (C.rotate k)) :
    IsWebOn G S C := by
  obtain ⟨hs, R, tri, hRS, hrib, htri⟩ := h
  exact ⟨hs, R, tri, hRS, hrib.of_rotate, htri⟩

namespace Case2

variable {S : Set V} {x y z ℓ : V} {L P : List V}

/-- `P L` is a cycle of `G[𝒞 ∪ P]`. -/
theorem isCycleList_H (hc : Case2 G S x y z ℓ L P) :
    IsCycleList (restrict G (compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P})) (P ++ L) := by
  obtain ⟨M, hM⟩ := hc.mu.1.exists_middle (hc.mu.1.two_le_length hc.cyc)
  have hnd := hc.cyc.2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  have h₁ : IsPathList G univ (x :: M ++ [z]) :=
    ⟨hM ▸ hc.mu.1.2.1, hM ▸ hc.mu.1.1, fun _ _ => trivial⟩
  have h₂ : IsPathList G univ (z :: L ++ [x]) := by
    have := (hc.cyc.rotate 2).isPathList (R := univ) fun _ _ => trivial
    have e : (x :: y :: z :: L).rotate 2 = (z :: L ++ [x]) ++ [y] := by
      simp [List.rotate_cons_succ]
    rw [e] at this
    exact this.prefix
  have hLne : L ≠ [] := List.ne_nil_of_mem hc.mem
  have hcyc := isCycleList_of_two_paths h₁ h₂ (fun v hv hvL => hc.mu.1.L_not_mem hc.cyc hvL
    (by rw [hM]; simp [hv])) hnd.1.2.1 (Or.inr hLne)
  have e : x :: M ++ z :: L = P ++ L := by rw [hM]; simp
  rw [e] at hcyc
  refine hcyc.restrict fun v hv => ?_
  rcases List.mem_append.mp hv with hv | hv
  · exact Or.inr hv
  · exact Or.inl (hc.mu.1.L_mem hc.cyc hc.sub hc.mem v hv)

/-- **`P` stays induced** in any crossless completion `W` of `G[𝒞 ∪ P]` for `P L`: a chord
`P[i] P[j]` with `i + 2 ≤ j` and the path from `P[i+1]` through `𝒞` to `L` (Claim A) would cross. -/
theorem no_chord [Finite V] (hc : Case2 G S x y z ℓ L P) {W : SimpleGraph V}
    (hW : restrict G (compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P}) ≤ W)
    (hnc : ¬ IsCrossed W (P ++ L)) {i j : ℕ} (hij : i + 2 ≤ j) (hj : j < P.length) :
    ¬ W.Adj (P[i]'(by omega)) P[j] := by
  classical
  intro hadj
  have hnd := hc.mu.1.2.1
  obtain ⟨c, hcK, hadjc⟩ := hc.mu.claim_A hc.max hc.cyc hc.sub hc.mem (i + 1) (by omega)
  obtain ⟨Wk⟩ := hcK.symm
  have hWK : ∀ w ∈ Wk.support, w ∈ compOf G S {v | v ∈ P} ℓ := fun w hw =>
    hcK.trans (Wk.takeUntil w hw).reachable
  obtain ⟨α, l, β, hsplit, hlL, hαL⟩ := exists_first_mem (Z := {v | v ∈ L}) Wk.support
    ⟨ℓ, Wk.end_mem_support, hc.mem⟩
  have hch : (P[i + 1] :: Wk.support).IsChain G.Adj := by
    have h1 := Wk.isChain_adj_support.imp
      (fun a b (h : (restrict G (S \ {v | v ∈ P})).Adj a b) => h.1)
    rw [← Walk.cons_tail_support] at h1 ⊢
    exact List.isChain_cons_cons.mpr ⟨hadjc, h1⟩
  have e : P[i + 1] :: Wk.support = (P[i + 1] :: (α ++ [l])) ++ β := by rw [hsplit]; simp
  rw [e] at hch
  have hΛK : ∀ w ∈ α ++ [l], w ∈ compOf G S {v | v ∈ P} ℓ := fun w hw =>
    hWK w (by
      rw [hsplit]
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ hw
      · rw [List.mem_singleton.mp hw]
        exact List.mem_append_right _ List.mem_cons_self)
  have hΛ : (P[i + 1] :: (α ++ [l])).IsChain W.Adj :=
    (isChain_restrict (X := compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P}) hch.left_of_append
      fun w hw => by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact Or.inr (List.getElem_mem _)
        · exact Or.inl (hΛK w hw)).imp fun _ _ h => hW h
  obtain ⟨R, hR, hRs⟩ := exists_tPath_of_chain (T := P ++ L)
    (a := P[i + 1]'(by omega)) (b := l) hΛ rfl
    (by rw [← List.cons_append, List.getLast?_append]; simp)
    (List.mem_append_left _ (List.getElem_mem _)) (List.mem_append_right _ hlL) (fun u hu huT => by
      rcases List.mem_cons.mp hu with rfl | hu
      · exact Or.inl rfl
      · rcases List.mem_append.mp hu with hu | hu
        · exfalso
          rcases List.mem_append.mp huT with h' | h'
          · exact hc.K_not_mem (hΛK u (List.mem_append_left _ hu)) h'
          · exact hαL u hu h'
        · exact Or.inr (List.mem_singleton.mp hu))
  have hne : P[i]'(by omega) ≠ P[j] := fun e => by
    have := hnd.getElem_inj_iff.mp e
    omega
  have hQ : IsTPath W (P ++ L) (Walk.cons hadj Walk.nil) := by
    refine ⟨by simp [hne], by simp, by simp, fun u hu h1 h2 => ?_⟩
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hu
    rcases hu with rfl | rfl
    · exact absurd rfl h1
    · exact absurd rfl h2
  refine hnc (isCrossed_of_alternate' (alternate_chord hij hj hlL) _ R hQ hR ?_)
  intro u huQ huR
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at huQ
  rcases List.mem_cons.mp (hRs u huR) with rfl | hu
  · rcases huQ with e | e
    · have := hnd.getElem_inj_iff.mp e
      omega
    · have := hnd.getElem_inj_iff.mp e
      omega
  · rcases huQ with rfl | rfl
    · exact hc.K_not_mem (hΛK _ hu) (List.getElem_mem _)
    · exact hc.K_not_mem (hΛK _ hu) (List.getElem_mem _)

/-- **The second case of Lemma 4.3** (page 15), with the hypothesis `hgap` that `P L` (the paper's
`PzCx`) is crossless in `G[𝒞 ∪ P]`, which the paper does not prove and `Case2.gap` proves. The graph `G` is the union of
the fan `W₁` on the side of `y` and a completion `W₂` of `G[𝒞 ∪ P]`, a web by induction; both
contain `P` as an induced path, so `IsMaxCrosslessOn.eq_sup_of_pieces` makes `G` a web. -/
theorem isWebOn [Finite V] (hc : Case2 G S x y z ℓ L P)
    (hgap : ¬ IsCrossed (restrict G (compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P})) (P ++ L))
    (ih : ∀ (G' : SimpleGraph V) (S' : Set V) (C' : List V), S'.ncard < S.ncard →
      IsCycleList G' C' → (∀ v ∈ C', v ∈ S') → IsMaxCrosslessOn G' S' C' → IsWebOn G' S' C') :
    IsWebOn G S (x :: y :: z :: L) := by
  have hnd := hc.mu.1.2.1
  have hℓ : ℓ ∈ S \ {v | v ∈ P} := ⟨hc.ℓ_mem_S, hc.ℓ_not_mem⟩
  obtain ⟨M, hM⟩ := hc.mu.1.exists_middle (hc.mu.1.two_le_length hc.cyc)
  have hyK : y ∉ compOf G S {v | v ∈ P} ℓ := hc.mu.1.y_not_mem hc.max.2.1 hc.cyc hc.mem
  -- the side of `𝒞`: a completion of `G[𝒞 ∪ P]`, a web by induction
  obtain ⟨W₂, hle₂, hmax₂⟩ := exists_maxCrosslessOn
    (G := restrict G (compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P})) (fun _ _ h => h.2.1) hgap
  have hsub₂ : ∀ v ∈ P ++ L, v ∈ compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P} := fun v hv => by
    rcases List.mem_append.mp hv with hv | hv
    · exact Or.inr hv
    · exact Or.inl (hc.mu.1.L_mem hc.cyc hc.sub hc.mem v hv)
  have hlt : (compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P}).ncard < S.ncard := by
    refine Set.ncard_lt_ncard ⟨fun v hv => ?_, fun h' => ?_⟩ (Set.toFinite _)
    · rcases hv with hv | hv
      · exact hc.K_mem_S hv
      · exact hc.P_sub v hv
    · rcases h' (hc.sub y (by simp)) with h1 | h1
      · exact hyK h1
      · exact hc.y_not_mem h1
  have hweb₂ := ih W₂ _ (P ++ L) hlt (hc.isCycleList_H.mono hle₂) hsub₂ hmax₂
  have hweb₂' : IsWebOn W₂ (compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P}) (z :: L ++ x :: M) := by
    refine IsWebOn.of_rotate (k := (z :: L).length) ?_
    rw [List.rotate_append_length_eq]
    have e : x :: M ++ z :: L = P ++ L := by rw [hM]; simp
    rw [e]
    exact hweb₂
  -- the side of `y`: the fan
  obtain ⟨W₁, hweb₁, hle₁, hind₁⟩ := hc.fan_side
  have hweb₁' : IsWebOn W₁ (S \ compOf G S {v | v ∈ P} ℓ) (x :: [y] ++ z :: M.reverse) := by
    refine IsWebOn.of_rotate (k := 1) ?_
    have e : (x :: [y] ++ z :: M.reverse).rotate 1 = y :: P.reverse := by
      rw [hM]; simp [List.rotate_cons_succ]
    rw [e]
    exact hweb₁
  refine (hc.max.eq_sup_of_pieces (k := 0) (a := x) (b := z) (A := [y]) (B := L) (m := M)
    (S₁ := S \ compOf G S {v | v ∈ P} ℓ) (S₂ := compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P})
    (by simp) ?_ ?_ ?_ hweb₁' hweb₂' hle₁ (le_trans le_rfl hle₂) ?_ ?_).2
  · -- the two sides cover `S`
    ext v
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · rcases hv with hv | hv | hv
      · exact hv.1
      · exact hc.K_mem_S hv
      · exact hc.P_sub v hv
    · by_cases hvK : v ∈ compOf G S {v | v ∈ P} ℓ
      · exact Or.inr (Or.inl hvK)
      · exact Or.inl ⟨hv, hvK⟩
  · -- they meet in `P`
    rw [← hM]
    ext v
    refine ⟨fun ⟨⟨_, hvK⟩, hv⟩ => hv.resolve_left hvK, fun hv => ⟨⟨hc.P_sub v hv,
      fun hk => hc.K_not_mem hk hv⟩, Or.inr hv⟩⟩
  · -- every edge of `G` lies on one side
    intro u v huv
    have hu := hc.max.1 huv
    have hv := hc.max.1 huv.symm
    by_cases huK : u ∈ compOf G S {v | v ∈ P} ℓ
    · refine Or.inr ⟨Or.inl huK, ?_⟩
      by_cases hvP : v ∈ P
      · exact Or.inr hvP
      · exact Or.inl (compOf_adj hℓ huK ⟨hv, hvP⟩ huv)
    · by_cases hvK : v ∈ compOf G S {v | v ∈ P} ℓ
      · refine Or.inr ⟨?_, Or.inl hvK⟩
        by_cases huP : u ∈ P
        · exact Or.inr huP
        · exact absurd (compOf_adj hℓ hvK ⟨hu, huP⟩ huv.symm) huK
      · exact Or.inl ⟨⟨hu, huK⟩, hv, hvK⟩
  · rw [← hM]
    exact hind₁
  · -- `P` is induced in `W₂`
    rw [← hM]
    intro u hu v hv huv
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hu
    obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem hv
    have hne : t ≠ t' := fun e => by subst e; exact W₂.ne_of_adj huv rfl
    rcases (show t' = t + 1 ∨ t = t' + 1 ∨ t + 2 ≤ t' ∨ t' + 2 ≤ t by omega)
      with rfl | rfl | h' | h'
    · exact isListEdge_getElem P t ht'
    · exact (isListEdge_getElem P t' ht).symm
    · exact absurd huv (hc.no_chord hle₂ hmax₂.2.1 h' ht')
    · exact absurd huv.symm (hc.no_chord hle₂ hmax₂.2.1 h' ht)

end Case2

end GraphMinor.HP25
