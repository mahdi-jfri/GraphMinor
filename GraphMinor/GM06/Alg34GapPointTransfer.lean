module

public import GraphMinor.GM06.Alg34GapCrossing

/-!
# Moving points inside their boundary gaps

A boundary gap is connected. If it avoids two fixed points, moving a
point within that gap preserves its component after removing the fixed
pair. Apply this fact twice, interchanging the two crossing pairs in
between, to preserve crossing when all four gap points move. This
allows the supplied gap order to be read at the actual dual vertices.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S]

private theorem move_right {C A B : Set S} {a b p q p' q' : S}
    (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hAsub : A ⊆ C \ {a, b}) (hBsub : B ⊆ C \ {a, b})
    (hp : p ∈ A) (hq : q ∈ B) (hp' : p' ∈ A) (hq' : q' ∈ B)
    (hc : CrossesOn C a b p q) : CrossesOn C a b p' q' := by
  have heA : connectedComponentIn (C \ {a, b}) p = connectedComponentIn (C \ {a, b}) p' :=
    connectedComponentIn_eq (hA.subset_connectedComponentIn hp hAsub hp')
  have heB : connectedComponentIn (C \ {a, b}) q = connectedComponentIn (C \ {a, b}) q' :=
    connectedComponentIn_eq (hB.subset_connectedComponentIn hq hBsub hq')
  rcases hc with ⟨ha, hpC, hb, hqC, hab, hpq, hap, haq, hbp, hbq, hcc⟩
  have hcc' : connectedComponentIn (C \ {a, b}) p' ≠ connectedComponentIn (C \ {a, b}) q' := by
    rw [← heA, ← heB]
    exact hcc
  have hpC' := hAsub hp'
  have hqC' := hBsub hq'
  have hap' : a ≠ p' := fun he => hpC'.2 (Or.inl he.symm)
  have haq' : a ≠ q' := fun he => hqC'.2 (Or.inl he.symm)
  have hbp' : b ≠ p' := fun he => hpC'.2 (Or.inr he.symm)
  have hbq' : b ≠ q' := fun he => hqC'.2 (Or.inr he.symm)
  exact ⟨ha, hpC'.1, hb, hqC'.1, hab, fun he => hcc' (congrArg _ he),
    hap', haq', hbp', hbq', hcc'⟩

private theorem segment_pair_subset {C V : Set S} {k : ℕ}
    (segs : Fin k → Set S) (hs : ∀ i, segs i ∈ segmentsOf C V)
    (hinj : Function.Injective segs) (p : Fin k → S) (hp : ∀ i, p i ∈ segs i)
    {a b i : Fin k} (hia : i ≠ a) (hib : i ≠ b) :
    segs i ⊆ C \ {p a, p b} := by
  intro z hz
  have hzC : z ∈ C := by
    obtain ⟨⟨v, _, he⟩, _⟩ := hs i
    rw [← he] at hz
    exact (connectedComponentIn_subset _ _ hz).1
  refine ⟨hzC, ?_⟩
  rintro (he | he)
  · exact disjoint_left.mp (disjoint_of_mem_segmentsOf_ne (hs i) (hs a)
      (fun hh => hia (hinj hh))) hz (he ▸ hp a)
  · exact disjoint_left.mp (disjoint_of_mem_segmentsOf_ne (hs i) (hs b)
      (fun hh => hib (hinj hh))) hz (he ▸ hp b)

private theorem segment_preconnected {C V seg : Set S}
    (hs : seg ∈ segmentsOf C V) : IsPreconnected seg := by
  obtain ⟨⟨p, _, rfl⟩, _⟩ := hs
  exact isPreconnected_connectedComponentIn

private theorem transfer {C V : Set S} (hC : IsOArc C) {k : ℕ}
    (segs : Fin k → Set S) (hs : ∀ i, segs i ∈ segmentsOf C V)
    (hinj : Function.Injective segs) (p q : Fin k → S)
    (hp : ∀ i, p i ∈ segs i) (hq : ∀ i, q i ∈ segs i)
    (a b i j : Fin k) (hc : CrossesOn C (p a) (p b) (p i) (p j)) :
    CrossesOn C (q a) (q b) (q i) (q j) := by
  have hc' := hc
  rcases hc' with ⟨_, _, _, _, _, _, hai, haj, hbi, hbj, _⟩
  have hai' : a ≠ i := fun he => hai (congrArg p he)
  have haj' : a ≠ j := fun he => haj (congrArg p he)
  have hbi' : b ≠ i := fun he => hbi (congrArg p he)
  have hbj' : b ≠ j := fun he => hbj (congrArg p he)
  have h₁ := move_right (segment_preconnected (hs i)) (segment_preconnected (hs j))
    (segment_pair_subset segs hs hinj p hp hai'.symm hbi'.symm)
    (segment_pair_subset segs hs hinj p hp haj'.symm hbj'.symm)
    (hp i) (hp j) (hq i) (hq j) hc
  have h₂ := move_right (segment_preconnected (hs a)) (segment_preconnected (hs b))
    (segment_pair_subset segs hs hinj q hq hai' haj')
    (segment_pair_subset segs hs hinj q hq hbi' hbj')
    (hp a) (hp b) (hq a) (hq b) (h₁.comm hC)
  exact h₂.comm hC

/-- Choosing different points in the same enumerated boundary segments
preserves the entire four-point crossing order. -/
theorem gap_points_crosses_iff {C V : Set S} (hC : IsOArc C) {k : ℕ}
    (segs : Fin k → Set S) (hs : ∀ i, segs i ∈ segmentsOf C V)
    (hinj : Function.Injective segs) (p q : Fin k → S)
    (hp : ∀ i, p i ∈ segs i) (hq : ∀ i, q i ∈ segs i) (a b i j : Fin k) :
    CrossesOn C (p a) (p b) (p i) (p j) ↔ CrossesOn C (q a) (q b) (q i) (q j) :=
  ⟨transfer hC segs hs hinj p q hp hq a b i j,
    transfer hC segs hs hinj q p hq hp a b i j⟩

end GraphMinor.Compute.GM06DrawingRep
