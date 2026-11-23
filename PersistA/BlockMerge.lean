import LangtonsAnt

namespace LangtonsAnt.PersistA.BlockMerge

/-- Events in two consecutive proper subperiod blocks have no interleaving
between copies: normalized longitudinal position determines their order. -/
theorem cross_block_order {P cut i j k l r x y : Int}
    (hi0 : 0 <= i) (hic : i < cut) (hcj : cut <= j) (hjP : j < P)
    (hx : x = 2 * k + r) (hy : y = 2 * l + r - 1) :
    i - P * k < j - P * l ↔ y < x := by
  have hP : 0 <= P := by omega
  constructor
  · intro ht
    apply Classical.byContradiction
    intro hn
    have hkl : k + 1 <= l := by omega
    have hm := Int.mul_le_mul_of_nonneg_left hkl hP
    rw [Int.mul_add, Int.mul_one] at hm
    omega
  · intro hxy
    have hlk : l <= k := by omega
    have hm := Int.mul_le_mul_of_nonneg_left hlk hP
    omega

structure Chunk where
  initial : Bool
  odd : Bool

def Valid : Bool -> List Chunk -> Prop
  | _, [] => True
  | color, c :: cs => c.initial = color ∧ Valid (color ^^ c.odd) cs

def Linked : List Chunk -> Prop
  | [] => True
  | [_] => True
  | c :: d :: cs => d.initial = (c.initial ^^ c.odd) ∧ Linked (d :: cs)

def Ends : Bool -> List Chunk -> Bool
  | color, [] => color
  | color, c :: cs => Ends (color ^^ c.odd) cs

theorem valid_cons_iff (color : Bool) (c : Chunk) (cs : List Chunk) :
    Valid color (c :: cs) ↔ c.initial = color ∧ Linked (c :: cs) := by
  induction cs generalizing color c with
  | nil => simp [Valid, Linked]
  | cons d ds ih =>
      change (c.initial = color ∧ Valid (color ^^ c.odd) (d :: ds)) ↔
        c.initial = color ∧ d.initial = (c.initial ^^ c.odd) ∧ Linked (d :: ds)
      rw [ih]
      constructor
      · rintro ⟨hc, hd, hs⟩
        exact ⟨hc, by simpa only [hc] using hd, hs⟩
      · rintro ⟨hc, hd, hs⟩
        exact ⟨hc, by simpa only [hc] using hd, hs⟩

theorem valid_append (color : Bool) (xs ys : List Chunk) :
    Valid color (xs ++ ys) ↔ Valid color xs ∧ Valid (Ends color xs) ys := by
  induction xs generalizing color with
  | nil => simp [Valid, Ends]
  | cons c cs ih =>
      simp only [List.cons_append, Valid, Ends, ih]
      exact and_assoc.symm

theorem linked_white_iff (c : Chunk) (cs : List Chunk) :
    Valid false (c :: cs) ↔ c.initial = false ∧ Linked (c :: cs) :=
  valid_cons_iff false c cs


end LangtonsAnt.PersistA.BlockMerge
