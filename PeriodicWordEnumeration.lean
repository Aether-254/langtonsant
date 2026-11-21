import PeriodicWordCore

namespace LangtonsAnt

def encodedWord {P : Nat} (c : Fin (2 ^ P)) (i : Nat) : Bool := c.val.testBit i

def encodeWord (P : Nat) (w : Nat -> Bool) : Fin (2 ^ P) :=
  ⟨(BitVec.ofBoolListLE ((List.range P).map w)).toNat, by
    simpa using (BitVec.ofBoolListLE ((List.range P).map w)).isLt⟩

theorem encodedWord_encodeWord {P : Nat} (w : Nat -> Bool) {i : Nat} (hi : i < P) :
    encodedWord (encodeWord P w) i = w i := by
  simp [encodedWord, encodeWord, BitVec.testBit_toNat, List.getD_eq_getElem?_getD,
    List.getElem?_range hi]

def checkNoWords (P : Nat) : Bool :=
  (List.range (2 ^ P)).all (fun c => !checkConsistentWord P (fun i => c.testBit i))

theorem checkNoWords_sound {P : Nat} (h : checkNoWords P = true) (w : Nat -> Bool) :
    ¬ ConsistentWord P w := by
  intro hc
  have he : ConsistentWord P (encodedWord (encodeWord P w)) :=
    hc.congr (fun j hj => (encodedWord_encodeWord w hj).symm)
  have hall := List.all_eq_true.mp h (encodeWord P w).val
    (List.mem_range.mpr (encodeWord P w).isLt)
  change (!checkConsistentWord P (encodedWord (encodeWord P w))) = true at hall
  rw [(checkConsistentWord_iff P _).mpr he] at hall
  contradiction

/-- A block of encodings, so independent kernel certificates can bound peak memory. -/
def checkNoWordsRange (P start count : Nat) : Bool :=
  (List.range count).all (fun c => !checkConsistentWord P (fun i => (start + c).testBit i))

theorem checkNoWordsRange_sound {P start count : Nat} (h : checkNoWordsRange P start count = true)
    {c : Nat} (hlo : start <= c) (hhi : c < start + count) :
    checkConsistentWord P (fun i => c.testBit i) = false := by
  have hh := List.all_eq_true.mp h (c - start) (List.mem_range.mpr (by omega))
  have he : start + (c - start) = c := by omega
  rw [he] at hh
  cases hb : checkConsistentWord P (fun i => c.testBit i) <;> simp_all

theorem checkNoWords_of_blocks {P width blocks : Nat} (hw : 0 < width)
    (hsize : 2 ^ P <= width * blocks)
    (h : forall k, k < blocks -> checkNoWordsRange P (width * k) width = true) :
    checkNoWords P = true := by
  apply List.all_eq_true.mpr
  intro c hc
  have hlt : c < 2 ^ P := List.mem_range.mp hc
  have hk : c / width < blocks := by
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simpa only [Nat.mul_comm] using Nat.lt_of_lt_of_le hlt hsize
  have hh := Nat.div_add_mod c width
  have hm := Nat.mod_lt c hw
  have he := checkNoWordsRange_sound (h (c / width) hk) (c := c) (by omega) (by omega)
  simp [he]

end LangtonsAnt
