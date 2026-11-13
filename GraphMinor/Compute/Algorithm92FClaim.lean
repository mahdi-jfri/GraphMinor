module

public import GraphMinor.Compute.Algorithm92Input

/-!
# Graph Minors XIII, (9.2): the interface of the program that finds `F` (`Algorithm92FClaim.lean`)

Page 101 of Graph Minors XIII: "First, we determine $F$. This takes time $O(\varepsilon)$." The
program of (9.2) is split in two. The first part parses the input and finds `F`; the second part
(compression, table, output) reads what the first part wrote. This file states what the first part
must do, as the claim `F92ProgClaim`:

from `s.arrs inArr = encAlg92In x`, it writes `x.G.enc` into `a_G`, `x.W.encList` into `a_W`, and
`encSegs92 segs` into `a_F`, for a list `segs` of paths with `segs.length ≤ k` and
`IsFSystem x segs paths` for some `paths`; in time `≤ C * alg92Size x`, with `C` and the word size
constant `c` depending only on `l, m, p, h, k, r`. It may use the arrays `a_G`, `a_W`, `a_F` and any
array with index `≥ a_base`, and the registers `≥ r_base`.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

/-- The encoding of the paths of `F`: their number, then each path as its length followed by its
vertices. -/
def encSegs92 {n : ℕ} (segs : List (List (Fin n))) : List ℕ :=
  segs.length :: segs.flatMap (fun P => P.length :: P.map Fin.val)

/-- **The claim on the program that finds `F`** (to be proved by the parse and `F` programs). -/
def F92ProgClaim : Prop :=
  ∀ (l m p h k r : ℕ), 1 ≤ r →
    ∀ (a_G a_W a_F a_base : ℕ) (r_base : ℕ),
      inArr < a_base → a_G < a_base → a_W < a_base → a_F < a_base →
      inArr ≠ a_G → inArr ≠ a_W → inArr ≠ a_F → a_G ≠ a_W → a_G ≠ a_F → a_W ≠ a_F →
      ∃ (P : Cmd) (C c : ℕ), ∀ (w : ℕ) (x : Alg92Input l m p h k r) (s : State),
        wordSize c (alg92Size x) ≤ w →
        s.arrs inArr = encAlg92In x →
        ∃ s' t, Exec w P s s' t ∧ t ≤ C * alg92Size x ∧
          s'.arrs a_G = x.G.enc ∧
          s'.arrs a_W = x.W.encList ∧
          (∃ (segs : List (List (Fin x.n))) (paths : Fin k → List (Fin x.n)),
            IsFSystem x segs paths ∧ segs.length ≤ k ∧ s'.arrs a_F = encSegs92 segs) ∧
          (∀ a : ℕ, a < a_base → a ≠ a_G → a ≠ a_W → a ≠ a_F → s'.arrs a = s.arrs a) ∧
          (∀ q < r_base, s'.regs q = s.regs q)

end Alg92

end GraphMinor.Compute
