module

public import GraphMinor.Compute.GM06Alg34Input

/-!
# Reading the word array of a disc instance

Length prefixes delimit the endpoint, region, cuff, and division lists.
The reader returns natural-number labels. On an array produced by the
serializer it recovers every field, so two supplied data sets with the
same array are equal. No geometric object is chosen by the reader.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The drawing fields with natural-number labels, before checking their
bounds against the vertex and edge counts. -/
structure GM06RawDrawingData where
  n : ℕ
  ends : List (ℕ × ℕ)
  regions : List (List ℕ × List ℕ)
  cuffs : List (List ℕ)
  division : List (List ℕ)
  deriving DecidableEq, Repr

namespace GM06DrawingData

/-- Forget only the bounds on the supplied labels. -/
def raw (x : GM06DrawingData) : GM06RawDrawingData where
  n := x.n
  ends := x.ends.map (fun e => (e.1.val, e.2.val))
  regions := x.regions.map (fun r => (r.vertices.map Fin.val, r.edges.map Fin.val))
  cuffs := x.cuffs.map (List.map Fin.val)
  division := x.division.map (List.map Fin.val)

end GM06DrawingData

namespace GM06RawDrawingData

/-- Read one length-prefixed list and leave the remaining words. -/
def readList : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | k :: w => (w.take k, w.drop k)

/-- Read a given number of length-prefixed lists. -/
def readLists : ℕ → List ℕ → List (List ℕ) × List ℕ
  | 0, w => ([], w)
  | k + 1, w =>
    let (L, w') := readList w
    let (Ls, w'') := readLists k w'
    (L :: Ls, w'')

/-- Read the count and the corresponding group of lists. -/
def readGroup : List ℕ → List (List ℕ) × List ℕ
  | [] => ([], [])
  | k :: w => readLists k w

/-- Read a given number of endpoint pairs. -/
def readPairs : ℕ → List ℕ → List (ℕ × ℕ) × List ℕ
  | 0, w => ([], w)
  | k + 1, a :: b :: w =>
    let (es, w') := readPairs k w
    ((a, b) :: es, w')
  | _ + 1, _ => ([], [])

/-- Read the two boundary incidence lists for each region. -/
def readRegions : ℕ → List ℕ → List (List ℕ × List ℕ) × List ℕ
  | 0, w => ([], w)
  | k + 1, w =>
    let (vs, w') := readList w
    let (es, w'') := readList w'
    let (rs, w''') := readRegions k w''
    ((vs, es) :: rs, w''')

/-- Read a drawing array. Truncated arrays get default empty fields. The
round-trip theorem concerns valid supplied data and does not use defaults. -/
def read : List ℕ → GM06RawDrawingData
  | n :: m :: r :: w =>
    let (ends, w₁) := readPairs m w
    let (regions, w₂) := readRegions r w₁
    let (cuffs, w₃) := readGroup w₂
    let (division, _) := readGroup w₃
    ⟨n, ends, regions, cuffs, division⟩
  | _ => ⟨0, [], [], [], []⟩

private def pairWords (e : ℕ × ℕ) : List ℕ := [e.1, e.2]

private def regionWords (r : List ℕ × List ℕ) : List ℕ :=
  GM06DrawingData.listWords r.1 ++ GM06DrawingData.listWords r.2

private def rawWords (x : GM06RawDrawingData) : List ℕ :=
  [x.n, x.ends.length, x.regions.length] ++ x.ends.flatMap pairWords ++
    x.regions.flatMap regionWords ++ GM06DrawingData.listsWords x.cuffs ++
    GM06DrawingData.listsWords x.division

private theorem readList_words (L tail : List ℕ) :
    readList (GM06DrawingData.listWords L ++ tail) = (L, tail) := by
  simp [readList, GM06DrawingData.listWords]

private theorem readLists_words (Ls : List (List ℕ)) (tail : List ℕ) :
    readLists Ls.length (Ls.flatMap GM06DrawingData.listWords ++ tail) = (Ls, tail) := by
  induction Ls with
  | nil => rfl
  | cons L Ls ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readLists]
    rw [readList_words, ih]

private theorem readGroup_words (Ls : List (List ℕ)) (tail : List ℕ) :
    readGroup (GM06DrawingData.listsWords Ls ++ tail) = (Ls, tail) := by
  exact readLists_words Ls tail

private theorem readPairs_words (es : List (ℕ × ℕ)) (tail : List ℕ) :
    readPairs es.length (es.flatMap pairWords ++ tail) = (es, tail) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp [pairWords, readPairs, ih]

private theorem readRegions_words (rs : List (List ℕ × List ℕ)) (tail : List ℕ) :
    readRegions rs.length (rs.flatMap regionWords ++ tail) = (rs, tail) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.length_cons, List.flatMap_cons, regionWords, List.append_assoc,
      readRegions]
    rw [readList_words, readList_words, ih]

private theorem read_rawWords (x : GM06RawDrawingData) : read (rawWords x) = x := by
  cases x with
  | mk n es rs cs ds =>
    simp only [rawWords, List.cons_append, List.nil_append, List.append_assoc, read]
    rw [readPairs_words, readRegions_words, readGroup_words]
    have hd := readGroup_words ds []
    simp only [List.append_nil] at hd
    rw [hd]

end GM06RawDrawingData

namespace GM06DrawingData

private theorem raw_words (x : GM06DrawingData) :
    x.words = GM06RawDrawingData.rawWords x.raw := by
  simp only [words, raw, GM06RawDrawingData.rawWords, List.length_map,
    List.flatMap_map, GM06RawDrawingData.pairWords, GM06RawDrawingData.regionWords]

/-- The reader recovers every supplied field from its word array. -/
theorem read_words (x : GM06DrawingData) : GM06RawDrawingData.read x.words = x.raw := by
  rw [raw_words]
  exact GM06RawDrawingData.read_rawWords x.raw

private theorem finLists_injective {n : ℕ} :
    Function.Injective (List.map (List.map (Fin.val : Fin n → ℕ))) :=
  List.map_injective_iff.mpr (List.map_injective_iff.mpr Fin.val_injective)

private theorem finPairs_injective {n : ℕ} :
    Function.Injective (List.map (fun e : Fin n × Fin n => (e.1.val, e.2.val))) := by
  apply List.map_injective_iff.mpr
  intro a b h
  exact Prod.ext (Fin.val_injective (congrArg Prod.fst h))
    (Fin.val_injective (congrArg Prod.snd h))

private theorem regionLists_injective {n m : ℕ} :
    Function.Injective (List.map (fun r : GM06RegionBoundary n m =>
      (r.vertices.map Fin.val, r.edges.map Fin.val))) := by
  apply List.map_injective_iff.mpr
  rintro ⟨vs, es⟩ ⟨vs', es'⟩ h
  have hv := (List.map_injective_iff.mpr Fin.val_injective) (congrArg Prod.fst h)
  have he := (List.map_injective_iff.mpr Fin.val_injective) (congrArg Prod.snd h)
  cases hv
  cases he
  rfl

/-- Forgetting label bounds loses no data. Proofs of the bounds do not
change the vertex or edge labels. -/
theorem raw_injective : Function.Injective raw := by
  rintro ⟨n, es, rs, cs, ds⟩ ⟨n', es', rs', cs', ds'⟩ h
  have hn : n = n' := congrArg GM06RawDrawingData.n h
  subst n'
  have he := finPairs_injective (congrArg GM06RawDrawingData.ends h)
  dsimp only [raw] at he
  subst es'
  have hr := regionLists_injective (congrArg GM06RawDrawingData.regions h)
  dsimp only [raw] at hr
  subst rs'
  have hc := finLists_injective (congrArg GM06RawDrawingData.cuffs h)
  dsimp only [raw] at hc
  subst cs'
  have hd := finLists_injective (congrArg GM06RawDrawingData.division h)
  dsimp only [raw] at hd
  subst ds'
  rfl

/-- A supplied word array determines all of its finite drawing data. -/
theorem words_injective : Function.Injective words := by
  intro x y h
  apply raw_injective
  have hr := congrArg GM06RawDrawingData.read h
  simpa only [read_words] using hr

end GM06DrawingData
end GraphMinor.Compute
