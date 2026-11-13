module

public import GraphMinor.HP25.Lemma43Case2
public import GraphMinor.HP25.Lemma41
import GraphMinor.HP25.Lemma43Case1
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Gap43

/-!
# Lemma 4.3 and Theorem 1.3

Humeau and Pous, Lemma 4.3 (page 13): "Let $G$ be a graph with a cycle $C$. If $G$ is maximally
$C$-crossless, then $G$ is a web with frame $C$." Theorem 1.3 (page 2): "Let $G$ be a graph with a
cycle $C$. The following are equivalent: - $G$ is a web with frame $C$, - $G$ is maximally
$C$-crossless." and, on page 15, "Combining Lemmas 4.1 and 4.3 with Proposition 3.2, Theorem 1.3 is
proved."

We prove the vertex-set form `lemma_4_3_on` by strong induction on the number of vertices, as the
paper does ("We proceed by induction on $|G|$"). Write `C = x y z L`. If `x` and `z` are not
`C`-connected, this is the first case (`lemma_4_3_case_one`). Otherwise there is a path from `x`
to `z` inner disjoint from `C`, we take one minimal for the measure `μ` (`exists_isMuMin`), and this
is the second case (`Case2.isWebOn`). The paper splits on whether all pairs of vertices of `C` are
`C`-connected; the second case only uses the pair `x`, `z`.

The second case needs the statement `Lemma43Gap`: the cycle `PzCx` is crossless in `G[𝒞 ∪ P]`.
The paper uses this without proof. We prove it in `HP25/Gap43.lean` (`Case2.gap`) with the two
paths theorem of Graph Minors XIII, (8.5), so Lemma 4.3 and Theorem 1.3 have no extra hypothesis.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*}

/-- **The open step of Lemma 4.3.** In the setting of the second case (`Case2`), the cycle `P L`
(the paper's `PzCx`) is crossless in the graph induced by the component `𝒞_C^P` and `P`. The
paper needs this to apply induction to "a graph $H$ (the orange area above the triangular shapes)
containing $PzCx$ as a cycle" (page 15), but does not prove it. We prove it in `lemma43Gap_proved`. -/
@[expose] def Lemma43Gap (V : Type*) : Prop :=
  ∀ (G : SimpleGraph V) (S : Set V) (x y z ℓ : V) (L P : List V), Case2 G S x y z ℓ L P →
    ¬ IsCrossed (restrict G (compOf G S {v | v ∈ P} ℓ ∪ {v | v ∈ P})) (P ++ L)

/-- **The step of Lemma 4.3 that the paper leaves open holds** (`Case2.gap`). -/
theorem lemma43Gap_proved [Finite V] : Lemma43Gap V :=
  fun _ _ _ _ _ _ _ _ hc => hc.gap

variable {G : SimpleGraph V}

/-- **Lemma 4.3 on a vertex set.** A graph on `S` that is maximally crossless on `S` for a cycle
`C` is a web on `S` with frame `C`. -/
theorem lemma_4_3_on [Finite V] :
    ∀ (n : ℕ) (G : SimpleGraph V) (S : Set V) (C : List V), S.ncard = n → IsCycleList G C →
      (∀ v ∈ C, v ∈ S) → IsMaxCrosslessOn G S C → IsWebOn G S C := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G S C hn hC hCS h
  have ih' : ∀ (G' : SimpleGraph V) (S' : Set V) (C' : List V), S'.ncard < S.ncard →
      IsCycleList G' C' → (∀ v ∈ C', v ∈ S') → IsMaxCrosslessOn G' S' C' → IsWebOn G' S' C' :=
    fun G' S' C' hlt => ih _ (hn ▸ hlt) G' S' C' rfl
  match C, hC, hCS, h with
  | [], hC, _, _ => exact absurd hC.1 (by simp)
  | [_], hC, _, _ => exact absurd hC.1 (by simp)
  | [_, _], hC, _, _ => exact absurd hC.1 (by simp)
  | x :: y :: z :: L, hC, hCS, h =>
    by_cases hL : L = []
    · subst hL
      exact h.isWebOn_three hC hCS
    have hnd := hC.2.1
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    by_cases hconn : IsConnectedAvoiding G {v | v ∈ x :: y :: z :: L} x {z}
    · -- second case: a path from `x` to `z` inner disjoint from `C`
      obtain ⟨z', hz', p, hp, hin⟩ := hconn
      rw [mem_singleton_iff] at hz'
      subst hz'
      have hXZ : IsXZPath G (x :: y :: z' :: L) x z' p.support :=
        ⟨p.isChain_adj_support, hp.support_nodup, Walk.support_head? p, Walk.support_getLast? p,
          fun v hv hvC => by
            by_contra hne
            push Not at hne
            exact hin v hv hne.1 hne.2 hvC⟩
      obtain ⟨ℓ, L', rfl⟩ := List.exists_cons_of_ne_nil hL
      obtain ⟨P, hmu⟩ := exists_isMuMin S ℓ ⟨_, hXZ⟩
      have hc : Case2 G S x y z' ℓ (ℓ :: L') P := ⟨h, hC, hCS, by simp, hmu⟩
      exact hc.isWebOn hc.gap ih'
    · -- first case: `x` and `z` are not `C`-connected
      exact lemma_4_3_case_one ih' h hC hCS (by simp) (by simp) hnd.1.2.1 hconn

/-- **Lemma 4.3** (page 13): "Let $G$ be a graph with a cycle $C$. If $G$ is maximally
$C$-crossless, then $G$ is a web with frame $C$." -/
theorem lemma_4_3 [Finite V] {C : List V} (hC : IsCycleList G C)
    (h : IsMaximallyCrossless G C) : IsWeb G C :=
  lemma_4_3_on _ G univ C rfl hC (fun _ _ => trivial) (isMaxCrosslessOn_univ_iff.mpr h)

/-- **Theorem 1.3** (Generalised two paths theorem, page 2): "Let $G$ be a graph with a cycle $C$.
The following are equivalent: - $G$ is a web with frame $C$, - $G$ is maximally $C$-crossless."
The direction from webs uses Proposition 3.2 and Lemma 4.1 (`IsWeb.isMaximallyCrossless`), the
other direction Lemma 4.3. -/
theorem theorem_1_3 [Finite V] {C : List V} (hC : IsCycleList G C) :
    IsWeb G C ↔ IsMaximallyCrossless G C :=
  ⟨IsWeb.isMaximallyCrossless, lemma_4_3 hC⟩

end GraphMinor.HP25
