module

public import GraphMinor.Compute.F92Bounds
public import GraphMinor.Compute.F92Build

/-!
# The program that finds `F` in (9.2)

Parse and mark the input, find one subwall path by breadth-first search, build the segments
by first intersections in reverse input order, then encode the segment arrays. The proved
construction gives `IsFSystem`. Uniform word and cost bounds close `F92ProgClaim` without
assuming any of the program's steps.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- A search block above all caller addresses, marked subwalls and segment arrays. -/
def f92ScratchBase (a_base r_base k : ℕ) : ℕ := a_base + r_base + 4 * k + 113

/-- The complete parsing and `F` construction program. -/
def f92Prog (h k a_G a_W a_F a_base r_base : ℕ) : Cmd :=
  let base := f92ScratchBase a_base r_base k
  .seq (f92PreparePathsProg h k a_G a_W a_base r_base base)
    (.seq (f92BuildProg k a_base r_base (base + 80))
      (f92EncodeProg k a_base a_F (base + 80)))

/-- The Word RAM program required for the first part of Graph Minors XIII, (9.2),
page 101: from the encoded input, find and write a bounded `F` in linear time.
All step correctness, existence, cost and word bounds are proved. -/
theorem f92ProgClaim_proved : F92ProgClaim := by
  intro l m p h k r hr a_G a_W a_F a_base r_base hin_lt hG_lt hW_lt hF_lt
    hIG hIW hIF hGW hGF hWF
  let base := f92ScratchBase a_base r_base k
  have hbase : 100 ≤ base := by dsimp [base, f92ScratchBase]; omega
  have hspace : a_base + 13 + 3 * k ≤ base := by dsimp [base, f92ScratchBase]; omega
  have hrbase : r_base < base := by dsimp [base, f92ScratchBase]; omega
  refine ⟨f92Prog h k a_G a_W a_F a_base r_base, f92TotalFactor h k, f92WordCoeff h k + 1, ?_⟩
  intro w x s hword hs
  obtain ⟨hw, hn, hh, hc, he, hin, hent, henc⟩ := f92_word_bounds x hword
  have hn' : x.n < 2 ^ w := by omega
  have hw' : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, P, hex₁, ht₁, hG₁, hW₁, hrn₁, hH₁, hpaths₁, harr₁, hreg₁⟩ :=
    f92PreparePathsProg_exec x a_G a_W a_base r_base base hin_lt hG_lt hW_lt hIG hIW hGW
      hbase hspace hrbase hw hn hh hc he hin hent hs
  have hP : ∀ i, IsSubwallHPath x.W (x.W_sub i) (P i) := fun i => (hpaths₁ i).1
  obtain ⟨s₂, t₂, hex₂, ht₂, hsegs₂, hsegeq, harr₂, hreg₂⟩ :=
    f92BuildProg_exec x hr P hP a_base r_base (base + 80) hw' hn' hrn₁ hH₁
      (fun i => (hpaths₁ i).2)
  let Q := f92SegmentAt x.W P
  have hQlen : ∀ i, (Q i).length ≤ x.n := by
    intro i
    have hlen : (P i).length ≤ x.n := by
      obtain ⟨_, _, hnd, _⟩ := (hP i).1
      simpa using hnd.length_le_card
    exact (length_f92Prefix_le _ _ _).trans hlen
  obtain ⟨s₃, t₃, hex₃, ht₃, hout₃, harr₃, hreg₃⟩ :=
    f92EncodeProg_exec Q hQlen a_base a_F (base + 80) hF_lt hw' hn' henc hsegs₂
  have hlow₂ (a : ℕ) (ha : a < a_base) : s₂.arrs a = s₁.arrs a :=
    harr₂ a (by f92_omega) (fun i _ => by dsimp [aSeg92]; f92_omega)
  have hcost := f92TotalCost_le x
  unfold f92ParseFactor at hcost
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    (harr₃ a_G hG_lt hGF).trans ((hlow₂ a_G hG_lt).trans hG₁),
    (harr₃ a_W hW_lt hWF).trans ((hlow₂ a_W hW_lt).trans hW₁), ?_, ?_, ?_⟩
  · refine ⟨fSegs x P, fHPaths x P, isFSystem_fSegs x hr hP,
      le_of_eq (length_fSegs x hr hP), ?_⟩
    rw [hout₃, show List.ofFn Q = fSegs x P from hsegeq]
  · intro a ha haG haW haF
    exact (harr₃ a ha haF).trans ((hlow₂ a ha).trans (harr₁ a ha haG haW))
  · intro q hq
    exact (hreg₃ q (by omega)).trans ((hreg₂ q (by omega)).trans (hreg₁ q hq))

end GraphMinor.Compute.Alg92
