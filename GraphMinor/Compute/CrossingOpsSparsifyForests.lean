module

public import GraphMinor.Compute.CrossingOpsApexForests
public import GraphMinor.Compute.CrossingOpsCopy
import GraphMinor.Crossing.CutSec2Fan

/-!
# Preparing the four sparsification forests from an instance

A copy of the current instance supplies immutable adjacency lists for constructing
the apex graph. Four successive BFS passes then produce the parent arrays used
by the retention test. The original instance arrays remain unchanged.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- The instance copy used to prepare the apex graph. -/
def sparsifySourceArrs (A : ℕ) : InstArrs := ⟨A + 6, A, A + 1, A + 2, A + 7⟩

/-- Copy the instance and compute its four apex forests. -/
def sparsifyForestsProg (a : InstArrs) (A R : ℕ) : Cmd :=
  .seq (copyInstanceProg a (sparsifySourceArrs A) R) (apexFourForestProg a.cyc A R)

/-- From an instance and its valid cycle, compute the four forests and keep every
array below scratch memory. The sole numerical assumption is the word bound. -/
theorem sparsifyForestsProg_exec {w N : ℕ} (a : InstArrs) (A R : ℕ)
    (hok : ArrsOk a.list A) {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {s : State} (hinst : IsInstanceAt a G S D s)
    (hcyc : HP25.IsCycleList G D) (hw : 10 * instSize N G < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (ess : List (List (Fin (N + 1) × Fin (N + 1)))),
      Exec w (sparsifyForestsProg a A R) s s' t ∧ t ≤ 2060 * instSize N G ∧
      ess.length = 4 ∧ IsScanFirstSequence (apex G D) (apexVerts (↑S)) (apexForests ess) ∧
      (apexForests ess).length = 4 ∧
      (∀ i (hi : i < ess.length), IsBfsParentsAt (A + 10 + 10 * i + 4) ess[i] s') ∧
      (∀ x, x < A → s'.arrs x = s.arrs x) := by
  have hsz : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  have hDN : D.length ≤ N := by simpa using hcyc.2.1.length_le_card
  have hok' : ArrsOk (a.list ++ (sparsifySourceArrs A).list) (A + 8) := by
    constructor
    · rw [List.nodup_append]
      refine ⟨hok.1, by simp [sparsifySourceArrs, InstArrs.list] <;> omega, ?_⟩
      intro x hx y hy
      have := hok.2 x hx
      simp [sparsifySourceArrs, InstArrs.list] at hy
      omega
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · have := hok.2 x hx; omega
      · simp [sparsifySourceArrs, InstArrs.list] at hx; omega
  obtain ⟨s1, t1, he1, ht1, hf1, hi1⟩ := copyInstanceProg_exec (w := w)
    a (sparsifySourceArrs A) (A + 8) R hok' hinst hDN (by omega)
  have ha1 : ∀ x, x < A → s1.arrs x = s.arrs x := by
    intro x hx
    apply hf1.2 x (by omega)
    simp [sparsifySourceArrs, InstArrs.list]; omega
  obtain ⟨lists, hadj⟩ := hi1.2.2.1
  obtain ⟨s2, t2, ess, he2, ht2, hlen, hseq, hflen, hp, ha2⟩ :=
    apexFourForestProg_exec (w := w) a.cyc A R S (hok.2 _ (by simp [InstArrs.list]))
      hinst.1 hadj hi1.2.2.2.1
      ((ha1 _ (hok.2 _ (by simp [InstArrs.list]))).trans hinst.2.2.2.2)
      hcyc.2.1 (fun v hv => mem_of_mem_cycleList hinst.1 hcyc hv) hi1.2.1 (by exact hw)
  refine ⟨s2, t1 + t2, ess, .seq he1 he2, by omega, hlen, hseq, hflen, hp, ?_⟩
  exact fun x hx => (ha2 x hx).trans (ha1 x hx)

/-- The four indexed parent arrays form the list of parent encodings used by retention. -/
theorem sparsify_parents_forall₂ {N : ℕ} (A B : ℕ)
    {ess : List (List (Fin (N + 1) × Fin (N + 1)))} {s : State}
    (hlen : ess.length = 4) (hB : A + 44 < B)
    (hp : ∀ i (hi : i < ess.length), IsBfsParentsAt (A + 10 + 10 * i + 4) ess[i] s) :
    List.Forall₂ (fun a edges => a < B ∧ IsBfsParentsAt a edges s)
      [A + 10 + 4, A + 10 + 14, A + 10 + 24, A + 10 + 34] ess := by
  obtain ⟨e0, e1, e2, e3, rfl⟩ := List.length_eq_four.mp hlen
  have h0 := hp 0 (by simp)
  have h1 := hp 1 (by simp)
  have h2 := hp 2 (by simp)
  have h3 := hp 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
  refine .cons ⟨by omega, ?_⟩ (.cons ⟨by omega, ?_⟩ (.cons ⟨by omega, ?_⟩ (.cons ⟨by omega, ?_⟩ .nil)))
  · simpa [Nat.add_assoc] using h0
  · simpa [Nat.add_assoc] using h1
  · simpa [Nat.add_assoc] using h2
  · simpa [Nat.add_assoc] using h3

/-- A cycle's distinct vertices belong to the active set, so there are at least
three active vertices and the positive extra-edge quota is feasible in the dense case. -/
theorem sparsify_quota_bounds {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} (hG : HP25.IsSupportedOn G (↑S)) (hD : HP25.IsCycleList G D)
    (hdense : 16 * S.card < G.edgeSet.ncard) :
    3 ≤ S.card ∧ 0 < N ∧ 0 < 3 * S.card - 5 ∧ 3 * S.card - 5 ≤ G.edgeSet.ncard := by
  have hsub : D.toFinset ⊆ S := by
    intro v hv
    exact mem_of_mem_cycleList hG hD (List.mem_toFinset.mp hv)
  have hlen : D.length ≤ S.card := by
    simpa only [List.toFinset_card_of_nodup hD.2.1] using Finset.card_le_card hsub
  have hSN : S.card ≤ N := (S.card_le_univ).trans_eq (by simp)
  have hthree := hD.1
  omega

end GraphMinor.Compute.Crossing
