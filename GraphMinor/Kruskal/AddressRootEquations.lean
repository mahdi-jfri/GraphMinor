module

public import GraphMinor.Kruskal.AddressEmbedding

/-!
# Address embeddings with root and branch equations

The root construction maps the root to the root and prefixes the selected
branch index at all other vertices. We give these equations explicitly so
that labels can be tracked through the map. The common-ancestor proof
separates vertices in one branch from vertices in distinct branches.
-/

namespace GraphMinor.Kruskal.OrderedTree

private def rootAddressMap {ts us : List OrderedTree}
    (σ : Fin ts.length ↪ Fin us.length)
    (φ : ∀ i, AddressEmbedding ts[i] us[σ i]) :
    Option (Σ i : Fin ts.length, {p // p ∈ (ts[i]).addresses}) →
      {q // q ∈ (OrderedTree.node us).addresses}
  | none => ⟨[], nil_mem_addresses _⟩
  | some ⟨i, p⟩ => ⟨(σ i).val :: ((φ i).vertices p).val,
      (cons_mem_addresses_iff us (σ i).val _).2
        ⟨σ i, rfl, ((φ i).vertices p).property⟩⟩

private theorem rootAddressMap_injective {ts us : List OrderedTree}
    (σ : Fin ts.length ↪ Fin us.length)
    (φ : ∀ i, AddressEmbedding ts[i] us[σ i]) :
    Function.Injective (rootAddressMap σ φ) := by
  intro x y hxy
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      obtain ⟨i, p⟩ := y
      have h : ([] : List ℕ) = (σ i).val :: ((φ i).vertices p).val :=
        congrArg Subtype.val hxy
      cases h
  | some x =>
    obtain ⟨i, p⟩ := x
    cases y with
    | none =>
      have h : (σ i).val :: ((φ i).vertices p).val = ([] : List ℕ) :=
        congrArg Subtype.val hxy
      cases h
    | some y =>
      obtain ⟨j, q⟩ := y
      have h := List.cons.inj (congrArg Subtype.val hxy)
      have hij : i = j := σ.injective (Fin.ext h.1)
      subst j
      have hpq : p = q := (φ i).vertices.injective (Subtype.ext h.2)
      subst q
      rfl

private noncomputable def rootVertices {ts us : List OrderedTree}
    (σ : Fin ts.length ↪ Fin us.length)
    (φ : ∀ i, AddressEmbedding ts[i] us[σ i]) :
    {p // p ∈ (OrderedTree.node ts).addresses} ↪
      {q // q ∈ (OrderedTree.node us).addresses} :=
  (branchAddressEquiv ts).symm.toEmbedding.trans
    ⟨rootAddressMap σ φ, rootAddressMap_injective σ φ⟩

private theorem rootVertices_apply {ts us : List OrderedTree}
    (σ : Fin ts.length ↪ Fin us.length)
    (φ : ∀ i, AddressEmbedding ts[i] us[σ i])
    (x : Option (Σ i : Fin ts.length, {p // p ∈ (ts[i]).addresses})) :
    rootVertices σ φ (branchAddress ts x) = rootAddressMap σ φ x := by
  change rootAddressMap σ φ ((branchAddressEquiv ts).symm (branchAddressEquiv ts x)) = _
  rw [Equiv.symm_apply_apply]

public section

/-- Changing the tree expressions preserves the address values of an embedding. -/
@[expose] def AddressEmbedding.changeTrees {s t s' t' : OrderedTree}
    (φ : AddressEmbedding s t) (hs : s = s') (ht : t = t') :
    AddressEmbedding s' t' where
  vertices := {
    toFun p := ⟨(φ.vertices ⟨p.val, by simpa only [hs] using p.property⟩).val,
      by simpa only [ht] using
        (φ.vertices ⟨p.val, by simpa only [hs] using p.property⟩).property⟩
    inj' := by
      intro p q h
      have he : φ.vertices ⟨p.val, by simpa only [hs] using p.property⟩ =
          φ.vertices ⟨q.val, by simpa only [hs] using q.property⟩ :=
        Subtype.ext (congrArg (fun z : {p // p ∈ t'.addresses} ↦ z.val) h)
      have hi := φ.vertices.injective he
      exact Subtype.ext (congrArg (fun z : {p // p ∈ s.addresses} ↦ z.val) hi) }
  meet_eq p q := φ.meet_eq
    ⟨p.val, by simpa only [hs] using p.property⟩
    ⟨q.val, by simpa only [hs] using q.property⟩

/-- An injection between branches and embeddings of the selected branches
give a root-preserving embedding of the whole trees. -/
noncomputable def AddressEmbedding.rootWithEquations {ts us : List OrderedTree}
    (σ : Fin ts.length ↪ Fin us.length)
    (φ : ∀ i, AddressEmbedding ts[i] us[σ i]) :
    AddressEmbedding (.node ts) (.node us) where
  vertices := rootVertices σ φ
  meet_eq p q := by
    obtain ⟨xp, rfl⟩ := (branchAddress_bijective ts).2 p
    obtain ⟨xq, rfl⟩ := (branchAddress_bijective ts).2 q
    cases xp with
    | none =>
      change addressMeet (rootVertices σ φ (branchAddress ts none)).val
        (rootVertices σ φ (branchAddress ts xq)).val =
          (rootVertices σ φ (branchAddress ts none)).val
      simp only [rootVertices_apply]
      rfl
    | some xp =>
      obtain ⟨i, p⟩ := xp
      cases xq with
      | none =>
        change addressMeet (rootVertices σ φ (branchAddress ts (some ⟨i, p⟩))).val
          (rootVertices σ φ (branchAddress ts none)).val =
            (rootVertices σ φ (branchAddress ts none)).val
        simp only [rootVertices_apply]
        rfl
      | some xq =>
        obtain ⟨j, q⟩ := xq
        by_cases hij : i = j
        · subst j
          let r : {p // p ∈ (ts[i]).addresses} :=
            ⟨addressMeet p.val q.val, (ts[i]).addressMeet_mem p.property⟩
          have hm : (⟨addressMeet (branchAddress ts (some ⟨i, p⟩)).val
              (branchAddress ts (some ⟨i, q⟩)).val,
              (OrderedTree.node ts).addressMeet_mem (branchAddress ts (some ⟨i, p⟩)).property⟩ :
                {p // p ∈ (OrderedTree.node ts).addresses}) =
                branchAddress ts (some ⟨i, r⟩) := by
            apply Subtype.ext
            simp only [addressMeet, ↓reduceIte, branchAddress, r]
          rw [hm]
          simp only [rootVertices_apply]
          change addressMeet ((σ i).val :: ((φ i).vertices p).val)
            ((σ i).val :: ((φ i).vertices q).val) =
              (σ i).val :: ((φ i).vertices r).val
          simp only [addressMeet, ↓reduceIte, (φ i).meet_eq, r]
        · have hijv : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
          have hσ : (σ i).val ≠ (σ j).val := fun h ↦ hij (σ.injective (Fin.ext h))
          have hm : (⟨addressMeet (branchAddress ts (some ⟨i, p⟩)).val
              (branchAddress ts (some ⟨j, q⟩)).val,
              (OrderedTree.node ts).addressMeet_mem (branchAddress ts (some ⟨i, p⟩)).property⟩ :
                {p // p ∈ (OrderedTree.node ts).addresses}) = branchAddress ts none := by
            apply Subtype.ext
            simp only [addressMeet, hijv, ↓reduceIte, branchAddress]
          rw [hm]
          simp only [rootVertices_apply]
          change addressMeet ((σ i).val :: ((φ i).vertices p).val)
            ((σ j).val :: ((φ j).vertices q).val) = []
          simp only [addressMeet, hσ, ↓reduceIte]

/-- The assembled address map sends the root to the root. -/
theorem AddressEmbedding.rootWithEquations_nil {ts us : List OrderedTree}
    (σ : Fin ts.length ↪ Fin us.length)
    (φ : ∀ i, AddressEmbedding ts[i] us[σ i]) :
    ((AddressEmbedding.rootWithEquations σ φ).vertices
      ⟨[], nil_mem_addresses _⟩).val = [] := by
  exact congrArg Subtype.val (rootVertices_apply σ φ none)

/-- On a branch, the assembled address map prefixes the chosen target index. -/
theorem AddressEmbedding.rootWithEquations_cons {ts us : List OrderedTree}
    (σ : Fin ts.length ↪ Fin us.length)
    (φ : ∀ i, AddressEmbedding ts[i] us[σ i]) (i : Fin ts.length)
    (p : {p // p ∈ (ts[i]).addresses}) :
    ((AddressEmbedding.rootWithEquations σ φ).vertices
      (branchAddress ts (some ⟨i, p⟩))).val =
        (σ i).val :: ((φ i).vertices p).val := by
  exact congrArg Subtype.val (rootVertices_apply σ φ (some ⟨i, p⟩))

end
end GraphMinor.Kruskal.OrderedTree
