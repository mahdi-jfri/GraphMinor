module

public import GraphMinor.Thomason.TruncatedTable

/-!
# Numeric tables for the twelve-vertex density bound

The first table is an integer edge potential on orders zero through
one hundred twenty. The second is the required minimum degree for
neighbourhood orders zero through forty-six. The third gives the nine
selection sizes for each neighbourhood order. Their properties are
proved by finite integer checks in the accompanying certificate files.
-/

@[expose] public section
namespace GraphMinor.Thomason

/-- Integer edge thresholds, clamped after order one hundred twenty. -/
def twelvePotentialValues : List ℕ :=
  [37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 46, 56, 66, 76, 87, 99, 111, 124, 137, 150, 164, 178, 193, 209, 225, 241, 257, 274, 291, 309, 327, 345, 363, 382, 401, 421, 441, 461, 482, 503, 524, 545, 566, 588, 610, 632, 654, 676, 699, 722, 745, 769, 793, 817, 841, 865, 889, 914, 939, 964, 989, 1014, 1039, 1064, 1090, 1116, 1142, 1168, 1195, 1222, 1249, 1276, 1304, 1332, 1360, 1388, 1416, 1444, 1472, 1500, 1529, 1558, 1587, 1616, 1646, 1676, 1706, 1736, 1766, 1796, 1826, 1856, 1887, 1918, 1949, 1980, 2011, 2042, 2073, 2104, 2135, 2166, 2198, 2230, 2262, 2294, 2326, 2358, 2390, 2422, 2454, 2486, 2518, 2551, 2584, 2617, 2650, 2683, 2716, 2749, 2782]

/-- The integer potential for the twelve-vertex density bound. -/
def twelvePotential : ℕ → ℕ := truncatedTable twelvePotentialValues 120

/-- Required minimum degrees at each neighbourhood order. -/
def twelveRequiredValues : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 11, 12, 13, 13, 14, 15, 16, 16, 17, 18, 18, 19, 20, 21, 21, 22, 22, 23, 24, 24, 25, 25, 26, 27, 28, 28, 29, 30, 30, 31, 31, 32, 32, 33, 33]

/-- The required degree, clamped after neighbourhood order forty-six. -/
def twelveRequired : ℕ → ℕ := truncatedTable twelveRequiredValues 46

/-- The selection sizes at successive stages for each neighbourhood order. -/
def twelveSelectionValues : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 2, 2],
   [1, 1, 1, 1, 1, 1, 1, 2, 2],
   [1, 1, 1, 1, 1, 1, 1, 2, 2],
   [1, 1, 1, 1, 1, 1, 2, 2, 2],
   [1, 1, 1, 1, 1, 1, 2, 2, 2],
   [1, 1, 1, 1, 1, 1, 2, 2, 2],
   [1, 1, 1, 1, 1, 1, 1, 2, 2],
   [1, 1, 1, 1, 1, 1, 2, 2, 2],
   [1, 1, 1, 1, 1, 1, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 2, 2, 2, 2, 3],
   [1, 1, 1, 1, 1, 2, 2, 2, 2],
   [1, 1, 1, 1, 2, 2, 2, 2, 3],
   [1, 1, 1, 1, 2, 2, 2, 2, 3],
   [1, 1, 1, 1, 2, 2, 2, 2, 3],
   [1, 1, 1, 1, 2, 2, 2, 2, 3],
   [1, 1, 1, 1, 2, 2, 2, 2, 3]]

/-- The selection size for a given neighbourhood order and stage. -/
def twelveSelection (N j : ℕ) : ℕ :=
  (twelveSelectionValues.getD (min N 46) []).getD j 1

end GraphMinor.Thomason
