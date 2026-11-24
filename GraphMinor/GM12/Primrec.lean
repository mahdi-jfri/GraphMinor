module

public import Mathlib.Computability.Partrec
public import GraphMinor.GM07.ExplicitV
public import GraphMinor.GM12.Section4Theorem43
public import GraphMinor.GM12.Section4Theorem44
public import GraphMinor.GM12.Section4Theorem45

/-!
# Primitive recursiveness of the GM07 and GM12 explicit bounds

This file collects shared `Primrec` combinators and primitive-recursiveness proofs for the
explicit bounds of Graph Minors VII (`GM07.wExplicit`, `GM07.wMaxExplicit`, `GM07.muExplicit`,
`GM07.vModelExplicit`) and Graph Minors XII (`GM12.theorem_3_1_bound`, `theorem_3_2_bound`,
`theorem_4_3_bound`, `theorem_4_4_bound`, `theorem_4_5_kBound`, `theorem_4_5_NBound`), shared by
`GraphMinor/GM13/Explicit.lean` and `GraphMinor/GM22/Explicit.lean`.
-/

public section

namespace GraphMinor.GM12.PrimrecHelpers

/-! ## Basic `Primrec` combinators -/

lemma primrec_pow₂ : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

lemma primrec_add {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a + g a :=
  Primrec.nat_add.comp hf hg

lemma primrec_sub {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a - g a :=
  Primrec.nat_sub.comp hf hg

lemma primrec_mul {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a * g a :=
  Primrec.nat_mul.comp hf hg

lemma primrec_div {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a / g a :=
  Primrec.nat_div.comp hf hg

lemma primrec_mod {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a % g a :=
  Primrec.nat_mod.comp hf hg

lemma primrec_max {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => max (f a) (g a) :=
  Primrec.nat_max.comp hf hg

lemma primrec_min {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => min (f a) (g a) :=
  Primrec.nat_min.comp hf hg

lemma primrec_pow {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a ^ g a :=
  primrec_pow₂.comp hf hg

lemma primrec_choose_two {α : Type} [Primcodable α] {f : α → ℕ} (hf : Primrec f) :
    Primrec fun a => (f a).choose 2 :=
  (primrec_div (primrec_mul hf (primrec_sub hf (Primrec.const 1))) (Primrec.const 2)).of_eq
    fun a => (Nat.choose_two_right (f a)).symm

lemma primrec_natRec {α β : Type} [Primcodable α] [Primcodable β]
    {n : α → ℕ} {z : α → β} {s : α → ℕ → β → β}
    (hn : Primrec n) (hz : Primrec z)
    (hs : Primrec fun q : α × ℕ × β => s q.1 q.2.1 q.2.2) :
    Primrec fun a => Nat.rec (motive := fun _ => β) (z a) (s a) (n a) :=
  Primrec.nat_rec' (h := fun a p => s a p.1 p.2) hn hz (Primrec₂.mk hs)

private lemma finset_range_sup_eq_natRec (n : ℕ) (f : ℕ → ℕ) :
    (Finset.range n).sup f = Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => max acc (f i)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.sup_insert, ih]
    change max (f n) _ = max _ (f n)
    exact max_comm _ _

lemma primrec_finset_range_sup {α : Type} [Primcodable α] {n : α → ℕ} {f : α → ℕ → ℕ}
    (hn : Primrec n) (hf : Primrec fun p : α × ℕ => f p.1 p.2) :
    Primrec fun a => (Finset.range (n a)).sup (f a) := by
  have hrec : Primrec fun a =>
      Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => max acc (f a i)) (n a) := by
    refine primrec_natRec hn (Primrec.const 0) ?_
    exact primrec_max (Primrec.snd.comp Primrec.snd)
      (hf.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
  exact hrec.of_eq fun a => (finset_range_sup_eq_natRec (n a) (f a)).symm

/-! ## GM07 explicit bounds -/

lemma primrec_wExplicit {α : Type} [Primcodable α]
    {a b c k n : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c)
    (hk : Primrec k) (hn : Primrec n) :
    Primrec fun x => GM07.wExplicit (a x) (b x) (c x) (k x) (n x) := by
  unfold GM07.wExplicit
  exact primrec_add
    (primrec_mul (primrec_mul (Primrec.const 2) hk)
      (primrec_pow (Primrec.const 3)
        (primrec_add (primrec_add (primrec_add (primrec_mul (Primrec.const 2) hn)
          (primrec_mul (Primrec.const 3) (primrec_add (primrec_mul (Primrec.const 2) ha) hb)))
          hc) hk)))
    hk

lemma primrec_wMaxExplicit {α : Type} [Primcodable α]
    {a b c k : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) (hk : Primrec k) :
    Primrec fun x => GM07.wMaxExplicit (a x) (b x) (c x) (k x) := by
  unfold GM07.wMaxExplicit
  have he : Primrec fun x => 2 * a x + b x + c x - 1 :=
    primrec_sub (primrec_add (primrec_add (primrec_mul (Primrec.const 2) ha) hb) hc) (Primrec.const 1)
  refine primrec_finset_range_sup (primrec_add (primrec_mul (Primrec.const 2) he) (Primrec.const 1)) ?_
  exact primrec_wExplicit (ha.comp Primrec.fst) (hb.comp Primrec.fst) Primrec.snd
    (primrec_mul (Primrec.const 2) (hk.comp Primrec.fst))
    (primrec_mul (Primrec.const 3) (he.comp Primrec.fst))

lemma primrec_muExplicit {α : Type} [Primcodable α]
    {a b c k : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) (hk : Primrec k) :
    Primrec fun x => GM07.muExplicit (a x) (b x) (c x) (k x) := by
  unfold GM07.muExplicit
  exact primrec_add
    (primrec_mul
      (primrec_mul (Primrec.const 2)
        (primrec_add (primrec_add (primrec_mul (Primrec.const 2) ha) hb) hc))
      (primrec_add hk (primrec_wMaxExplicit ha hb hc hk)))
    (primrec_mul (Primrec.const 2) hk)

lemma primrec_vModelExplicit {α : Type} [Primcodable α]
    {a b c k : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) (hk : Primrec k) :
    Primrec fun x => GM07.vModelExplicit (a x) (b x) (c x) (k x) := by
  unfold GM07.vModelExplicit
  exact primrec_add
    (primrec_mul
      (primrec_mul (Primrec.const 6)
        (primrec_sub (primrec_add (primrec_add (primrec_mul (Primrec.const 2) ha) hb) hc) (Primrec.const 1)))
      (primrec_add
        (primrec_add (primrec_wMaxExplicit ha hb hc hk)
          (primrec_mul (Primrec.const 2) (primrec_muExplicit ha hb hc hk)))
        (Primrec.const 1)))
    (primrec_mul (Primrec.const 2) hk)

/-! ## GM12 explicit bounds -/

lemma primrec_gm12_3_1 {α : Type} [Primcodable α]
    {a b t z : α → ℕ} (ha : Primrec a) (hb : Primrec b) (ht : Primrec t) (hz : Primrec z) :
    Primrec fun x => GM12.theorem_3_1_bound GM07.vModelExplicit (a x) (b x) (t x) (z x) := by
  unfold GM12.theorem_3_1_bound GM12.uniformAlphaBound
  have hzt1 : Primrec fun x => z x + t x + 1 :=
    primrec_add (primrec_add hz ht) (Primrec.const 1)
  exact primrec_mul (primrec_mul (Primrec.const 42) hzt1)
    (primrec_vModelExplicit ha hb (primrec_add ht (Primrec.const 1)) hzt1)

lemma primrec_gm12_3_2 {α : Type} [Primcodable α]
    {a b t z : α → ℕ} (ha : Primrec a) (hb : Primrec b) (ht : Primrec t) (hz : Primrec z) :
    Primrec fun x => GM12.theorem_3_2_bound GM07.vModelExplicit (a x) (b x) (t x) (z x) := by
  unfold GM12.theorem_3_2_bound GM12.theorem_3_2_sep_bound GM12.theorem_3_2_two_discs_bound
    GM12.theorem_3_2_three_discs_bound
  have hsep : Primrec fun x =>
      2 * max (GM12.theorem_3_1_bound GM07.vModelExplicit (a x) (b x) (t x) (z x)) (z x) + 1 :=
    primrec_add (primrec_mul (Primrec.const 2) (primrec_max (primrec_gm12_3_1 ha hb ht hz) hz))
      (Primrec.const 1)
  have h3 : Primrec fun x =>
      2 * max (42 * (z x + 3 + 1) * GM07.vModelExplicit (a x) (b x) (3 + 1) (z x + 3 + 1)) (z x) + 1 :=
    primrec_add
      (primrec_mul (Primrec.const 2)
        (primrec_max
          (primrec_mul
            (primrec_mul (Primrec.const 42)
              (primrec_add (primrec_add hz (Primrec.const 3)) (Primrec.const 1)))
            (primrec_vModelExplicit ha hb (Primrec.const 4)
              (primrec_add (primrec_add hz (Primrec.const 3)) (Primrec.const 1))))
          hz))
      (Primrec.const 1)
  exact primrec_max hsep (primrec_add (primrec_mul (Primrec.const 2) h3) (Primrec.const 1))

lemma primrec_gm12_4_3 {α : Type} [Primcodable α]
    {a b vB eB : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hv : Primrec vB) (he : Primrec eB) :
    Primrec fun x => GM12.theorem_4_3_bound GM07.vModelExplicit (a x) (b x) (vB x) (eB x) := by
  unfold GM12.theorem_4_3_bound GM12.feasibleControlBound
  refine primrec_finset_range_sup
    (primrec_add (primrec_add (primrec_mul (Primrec.const 4) hv) (primrec_mul (Primrec.const 4) he))
      (Primrec.const 1)) ?_
  have hk : Primrec fun p : α × ℕ =>
      max (GM12.theorem_3_2_bound GM07.vModelExplicit (a p.1) (b p.1) p.2 (2 * p.2))
        (2 * (3 * vB p.1 + eB p.1)) :=
    primrec_max
      (primrec_gm12_3_2 (ha.comp Primrec.fst) (hb.comp Primrec.fst) Primrec.snd
        (primrec_mul (Primrec.const 2) Primrec.snd))
      (primrec_mul (Primrec.const 2)
        (primrec_add (primrec_mul (Primrec.const 3) (hv.comp Primrec.fst)) (he.comp Primrec.fst)))
  exact primrec_max hk
    (primrec_add (Primrec.const 5) (primrec_mul Primrec.snd (primrec_add hk (Primrec.const 7))))

lemma primrec_gm12_4_4 {α : Type} [Primcodable α]
    {a b p : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hp : Primrec p) :
    Primrec fun x => GM12.theorem_4_4_bound GM07.vModelExplicit (a x) (b x) (p x) := by
  unfold GM12.theorem_4_4_bound GM12.theorem_4_4_large_bound GM12.vertexConnectionsBound
  have ht : Primrec fun x => 2 * (p x * (p x - 1) / 2) :=
    primrec_mul (Primrec.const 2)
      (primrec_div (primrec_mul hp (primrec_sub hp (Primrec.const 1))) (Primrec.const 2))
  exact primrec_max
    (primrec_add (primrec_max (primrec_gm12_3_2 ha hb ht ht) (primrec_mul (Primrec.const 2) hp))
      (Primrec.const 2))
    (primrec_gm12_4_3 ha hb (Primrec.const 2) (Primrec.const 1))

lemma primrec_gm12_4_5_k {α : Type} [Primcodable α] {p : α → ℕ} (hp : Primrec p) :
    Primrec fun x => GM12.theorem_4_5_kBound (p x) := by
  unfold GM12.theorem_4_5_kBound GM12.theorem_4_5_large_kBound
  have hp4 : Primrec fun x => max (p x) 4 := primrec_max hp (Primrec.const 4)
  exact primrec_pow
    (primrec_div (primrec_mul hp4 (primrec_sub hp4 (Primrec.const 1))) (Primrec.const 2))
    (Primrec.const 2)

lemma primrec_gm12_4_5_N {α : Type} [Primcodable α]
    {a b p : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hp : Primrec p) :
    Primrec fun x => GM12.theorem_4_5_NBound GM07.vModelExplicit (a x) (b x) (p x) := by
  unfold GM12.theorem_4_5_NBound GM12.theorem_4_5_large_NBound
  have hp4 : Primrec fun x => max (p x) 4 := primrec_max hp (Primrec.const 4)
  have hk : Primrec fun x => GM12.theorem_4_5_large_kBound (max (p x) 4) :=
    primrec_gm12_4_5_k hp
  exact primrec_max
    (primrec_finset_range_sup (primrec_add hk (Primrec.const 1))
      (primrec_gm12_3_2 (ha.comp Primrec.fst) (hb.comp Primrec.fst) Primrec.snd
        (primrec_mul (Primrec.const 4) Primrec.snd)))
    (primrec_add
      (primrec_mul (Primrec.const 2) (primrec_add hp4 (primrec_mul (Primrec.const 2) hk)))
      (Primrec.const 3))

end GraphMinor.GM12.PrimrecHelpers
