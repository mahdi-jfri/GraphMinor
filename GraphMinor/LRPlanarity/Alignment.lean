module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.ContourTree

/-!
# Weak alignment does not change satisfiability

This file proves `WeakAlignmentStatement`, following Part III of
`docs/planarity/planarity_test.tex`.

Call a back edge *nonisolated* when it occurs in a nontrivial equality or inequality of the
fork constraints. This means that it lies in a fork set together with a different back edge, or
that it lies in a fork set whose opposite set is nonempty. Take a coloring that satisfies the fork
constraints. We keep its colors on the nonisolated back edges and color every other pair `R`.
The fork constraints still hold, since they only compare nonisolated back edges.

For a tree edge `p = (u, v)`, let `M(p)` be the weak returns of `p` of minimum head depth. Suppose
that a member of `M(p)` lies in a fork set at a fork `w`. Then `w` is a strict ancestor of `v`,
and all of `M(p)` lies in that same fork set (`minWeakReturns_subset_forkSet`). So either all
members of `M(p)` keep their old colors, which agree, or all of them get color `R`.
-/

public section

namespace GraphMinor.LRPlanarity.Alignment

open SearchTree

variable {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}

/-- Part III: a back edge that occurs in a nontrivial equality or inequality of the fork
constraints. "Only distinct variables give a nontrivial equality." -/
def Nonisolated (T : Forest N) (G : SimpleGraph (Fin N)) (b : Arc N) : Prop :=
  ∃ v e f, T.Outgoing G v e ∧ T.Outgoing G v f ∧ e ≠ f ∧ b ∈ T.forkSet G e f ∧
    ((∃ c ∈ T.forkSet G e f, c ≠ b) ∨ (T.forkSet G f e).Nonempty)

/-- Part III: "we keep a satisfying coloring of every nonisolated variable and give every
isolated variable the color R." -/
noncomputable def recolor (T : Forest N) (G : SimpleGraph (Fin N)) (color : Coloring N) :
    Coloring N := by
  classical
  exact fun b => if Nonisolated T G b then color b else .right

theorem recolor_of_nonisolated (color : Coloring N) {b : Arc N} (hb : Nonisolated T G b) :
    recolor T G color b = color b := by
  simp [recolor, hb]

theorem recolor_of_isolated (color : Coloring N) {b : Arc N} (hb : ¬ Nonisolated T G b) :
    recolor T G color b = .right := by
  simp [recolor, hb]

/-- Part III: if a weak return `b` of `p` of minimum head depth lies in a fork set at a fork
`w`, then every weak return of `p` of minimum head depth lies in that fork set. "All members of
M(p) then belong to the same outgoing branch e of w, the one containing v, and have the same head
depth ell. So they all belong to the same set I(e,f)." -/
theorem minWeakReturns_subset_forkSet {p b : Arc N}
    (hb : b ∈ T.weakReturns G p) (hbmin : ∀ c ∈ T.weakReturns G p, T.depth b.2 ≤ T.depth c.2)
    {e f : Arc N} {v : Fin N} (he : T.Outgoing G v e)
    (hf : T.Outgoing G v f) (hbe : b ∈ T.forkSet G e f) {b' : Arc N}
    (hb' : b' ∈ T.weakReturns G p)
    (hb'min : ∀ c ∈ T.weakReturns G p, T.depth b'.2 ≤ T.depth c.2) :
    b' ∈ T.forkSet G e f := by
  obtain ⟨hbR, hlow⟩ := hbe
  obtain ⟨_, hvb, hbv⟩ := returns_spec hbR
  rw [he.1] at hvb hbv
  -- The other branch `f` has a return `c` of head depth `low f`, which is below `ell`.
  have hlowf : T.low G f < T.depth f.1 := by rw [hf.1]; omega
  obtain ⟨c, hcR, hcd⟩ := exists_returns_of_low_lt hlowf
  obtain ⟨hcb, hvc, _⟩ := returns_spec hcR
  rw [hf.1] at hvc
  -- The fork `v` is not in the subtree of `p.2`, or `c` would be a lower weak return.
  have hnot : ¬ T.Ancestor p.2 v := by
    intro h
    have hcW : c ∈ T.weakReturns G p := ⟨hcb, ancestor_trans h hvc, by
      have := hb.2.2; omega⟩
    have := hbmin c hcW
    omega
  have hvp : T.Ancestor v p.2 := by
    rcases ancestor_total hvb hb.2.1 with h | h
    · exact h
    · exact absurd h hnot
  -- So `b` does not start at `v`, and `e` is the tree edge on the path to `p.2`.
  obtain ⟨_, ⟨heb, rfl⟩ | ⟨heT, he2b, _⟩⟩ := hbR
  · exact absurd (he.1 ▸ hb.2.1) hnot
  have he2p : T.Ancestor e.2 p.2 := by
    rcases ancestor_total he2b hb.2.1 with h | h
    · exact h
    · by_cases hpe : p.2 = e.2
      · exact hpe ▸ ancestor_refl _
      · exact absurd (he.1 ▸ ancestor_of_ancestor_child heT h hpe) hnot
  have hdepth : T.depth b'.2 = T.depth b.2 := le_antisymm (hb'min b hb) (hbmin b' hb')
  refine ⟨⟨hb'.1, Or.inr ⟨heT, ancestor_trans he2p hb'.2.1, ?_⟩⟩, ?_⟩
  · rw [hdepth, he.1]; exact hbv
  · rw [hdepth]; exact hlow

/-- The recolored back edges in a fork set agree, since two distinct members of a fork set
are both nonisolated. -/
theorem recolor_monochromatic (color : Coloring N) (hc : T.ForkConstraints G color)
    {v : Fin N} {e f : Arc N} (he : T.Outgoing G v e) (hf : T.Outgoing G v f) (hef : e ≠ f) :
    Monochromatic (recolor T G color) (T.forkSet G e f) := by
  intro b hb b' hb'
  by_cases hbb : b = b'
  · rw [hbb]
  have hiso : Nonisolated T G b := ⟨v, e, f, he, hf, hef, hb, Or.inl ⟨b', hb', Ne.symm hbb⟩⟩
  have hiso' : Nonisolated T G b' := ⟨v, e, f, he, hf, hef, hb', Or.inl ⟨b, hb, hbb⟩⟩
  rw [recolor_of_nonisolated color hiso, recolor_of_nonisolated color hiso']
  exact (hc v e f he hf hef).1 b hb b' hb'

/-- The recoloring satisfies the fork constraints: "A set of the first kind is already
monochromatic". -/
theorem recolor_forkConstraints (color : Coloring N) (hc : T.ForkConstraints G color) :
    T.ForkConstraints G (recolor T G color) := by
  intro v e f he hf hef
  refine ⟨recolor_monochromatic color hc he hf hef,
    recolor_monochromatic color hc hf he (Ne.symm hef), ?_⟩
  intro b hb c hc'
  have hiso : Nonisolated T G b := ⟨v, e, f, he, hf, hef, hb, Or.inr ⟨c, hc'⟩⟩
  have hiso' : Nonisolated T G c := ⟨v, f, e, hf, he, Ne.symm hef, hc', Or.inr ⟨b, hb⟩⟩
  rw [recolor_of_nonisolated color hiso, recolor_of_nonisolated color hiso']
  exact (hc v e f he hf hef).2.2 b hb c hc'

/-- If one weak return of minimum head depth is nonisolated, the recoloring agrees on it and
on any other weak return of minimum head depth. -/
theorem recolor_eq_of_nonisolated (color : Coloring N) (hc : T.ForkConstraints G color)
    {p b b' : Arc N} (hb : b ∈ T.weakReturns G p)
    (hbmin : ∀ c ∈ T.weakReturns G p, T.depth b.2 ≤ T.depth c.2)
    (hb' : b' ∈ T.weakReturns G p)
    (hb'min : ∀ c ∈ T.weakReturns G p, T.depth b'.2 ≤ T.depth c.2)
    (hiso : Nonisolated T G b) : recolor T G color b = recolor T G color b' := by
  obtain ⟨v, e, f, he, hf, hef, hbe, _⟩ := hiso
  have hb'e := minWeakReturns_subset_forkSet hb hbmin he hf hbe hb' hb'min
  exact recolor_monochromatic color hc he hf hef b hbe b' hb'e

/-- The recoloring is weakly aligned: "It follows that each M(p) either is already forced
to be monochromatic by the original constraints, or consists entirely of variables that occur in no
nontrivial original equality or inequality." -/
theorem recolor_weakAlignment (color : Coloring N) (hc : T.ForkConstraints G color) :
    T.WeakAlignment G (recolor T G color) := by
  intro p _ b hb b' hb'
  by_cases hbb : b = b'
  · rw [hbb]
  by_cases hiso : Nonisolated T G b
  · exact recolor_eq_of_nonisolated color hc hb.1 hb.2 hb'.1 hb'.2 hiso
  by_cases hiso' : Nonisolated T G b'
  · exact (recolor_eq_of_nonisolated color hc hb'.1 hb'.2 hb.1 hb.2 hiso').symm
  rw [recolor_of_isolated color hiso, recolor_of_isolated color hiso']

end GraphMinor.LRPlanarity.Alignment

namespace GraphMinor.LRPlanarity

/-- Part III: "Thus the original fork constraints can be satisfied if and only if the fork
constraints together with *all* weak alignments can be satisfied." This holds for every
depth-first forest. -/
theorem weakAlignment_proved : WeakAlignmentStatement := by
  intro N G T _
  constructor
  · rintro ⟨color, hc⟩
    exact ⟨Alignment.recolor T G color, Alignment.recolor_forkConstraints color hc,
      Alignment.recolor_weakAlignment color hc⟩
  · rintro ⟨color, hc, _⟩
    exact ⟨color, hc⟩

end GraphMinor.LRPlanarity
