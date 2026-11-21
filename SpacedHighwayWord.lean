import SpacedObstacleHighway
import InfiniteHighwayPeriod

namespace LangtonsAnt

/-- A literal cache of the certified collision trace, checked against the actual finite run. -/
def collisionWordLiteral : Array Bool :=
  #[true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false,
    false, false, true, false, false, true, false, false, false, false, true, true, true, true, false, true,
    false, false, false, false, true, false, false, false, false, true, true, true, true, false, true, false,
    false, false, false, true, false, true, true, false, false, true, true, true, true, false, false, true,
    true, false, false, false, false, true, true, false, false, true, false, true, true, false, true, true,
    false, true, false, true, true, false, false, false, false, true, true, false, true, true, false, false,
    false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true,
    true, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true,
    true, true, false, true, false, false, false, false, true, false, false, false, false, true, true, true,
    true, false, true, false, false, false, false, true, false, true, true, false, false, true, true, true,
    true, false, false, true, true, false, false, false, false, true, true, false, false, true, false, true,
    true, false, true, true, false, true, false, true, true, false, false, false, false, true, true, false,
    true, false, false, false, false, true, false, false, false, false, true, true, true, true, false, true,
    false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, false,
    false, true, false, false, false, false, true, true, true, true, false, true, false, false, false, false,
    true, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true,
    false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, false,
    false, true, true, false, false, true, false, true, true, false, false, false, false, true, true, false,
    true, false, true, false, false, false, false, true, true, true, true, false, true, false, false, false,
    false, true, false, false, false, false, true, true, true, true, false, true, false, false, false, false,
    true, false, true, true, false, false, false, false, true, true, false, false, false, false, true, true,
    false, true, false, true, true, true, true, false, false, false, false, true, false, false, false, false,
    true, false, false, false, false, true, true, true, true, false, true, true, false, false, true, false,
    false, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false,
    false, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true,
    false, false, true, false, true, true, false, false, true, false, false, true, true, false, true, false,
    false, false, false, true, false, true, false, true, true, false, false, false, false, true, true, false,
    true, true, false, false, false, false, true, true, false, false, false, false, true, true, false, true,
    false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, false,
    false, true, false, false, false, false, true, true, true, true, false, true, false, false, false, false,
    true, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true,
    false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, false,
    false, true, true, false, false, true, false, true, true, false, true, true, false, true, false, true,
    true, false, false, false, false, true, true, false, true, true, false, false, false, false, true, true,
    false, false, false, false]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem collisionWord_trace_check : checkTrace chainCollisionSeed collisionWordLiteral.toList = true := by
  decide +kernel

theorem collisionWordLiteral_size : collisionWordLiteral.size = 548 := by decide +kernel

theorem obstacleWord_eq_literal : obstacleWord = collisionWordLiteral := by
  apply Array.ext
  · simp only [obstacleWord, List.size_toArray, finiteReadWord_length, collisionWordLiteral_size]
  · intro i hi hj
    have hi' : i < 548 := by simpa only [obstacleWord, List.size_toArray, finiteReadWord_length] using hi
    have hc := checkTrace_sound collisionWord_trace_check i (by simpa only [Array.length_toList, collisionWordLiteral_size] using hi')
    have hr := finiteReadWord_get chainCollisionSeed 548 i hi'
    have he : obstacleWord[i]?.getD false = collisionWordLiteral[i]?.getD false := by
      simpa only [obstacleWord, List.getElem?_toArray, Array.getElem?_toList] using hr.trans hc
    simpa only [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj, Option.getD_some] using he

def collisionWordBits : Nat := 43950238856594582275813850228710236923290054670221222073709419623383698863749189555191355581499223630419160961286400480895840082714135727715622369823035195362917643

def standardWordBits : Nat := 967482604049476582606230535435

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem collisionWord_bits_check :
    (List.range 548).all (fun n => collisionWordLiteral[n]?.getD false == collisionWordBits.testBit n) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem standardWord_bits_check :
    (List.range 104).all (fun n => highwayWord[n]?.getD false == standardWordBits.testBit n) = true := by
  decide +kernel

theorem obstacleColor_bits (n : Nat) : obstacleColor n = collisionWordBits.testBit (n % 548) := by
  have hh := (List.all_eq_true.mp collisionWord_bits_check) (n % 548)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simpa only [obstacleColor, obstacleWord_eq_literal, beq_iff_eq] using hh

theorem certifiedColor_bits (n : Nat) : certifiedColor n = standardWordBits.testBit (n % 104) := by
  have hh := (List.all_eq_true.mp standardWord_bits_check) (n % 104)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simpa only [certifiedColor, beq_iff_eq] using hh

/-- A collision block followed by k copies of the standard highway word. -/
def spacedColor (k n : Nat) : Bool :=
  let r := n % spacedPeriod k
  if r < 548 then obstacleColor r else certifiedColor (r - 548)

def collisionMarker : List Bool := [true, true, false, true, true, true]

def HasCollisionMarker (f : Nat -> Bool) (n : Nat) : Prop :=
  forall j : Fin 6, f (n + j.val) = collisionMarker[j.val]?.getD false

instance (f : Nat -> Bool) (n : Nat) : Decidable (HasCollisionMarker f n) :=
  inferInstanceAs (Decidable (forall j : Fin 6, f (n + j.val) = collisionMarker[j.val]?.getD false))

def markerAt (f : Nat -> Bool) (n : Nat) : Bool :=
  f n && f (n + 1) && (!f (n + 2)) && f (n + 3) && f (n + 4) && f (n + 5)

theorem markerAt_iff (f : Nat -> Bool) (n : Nat) : markerAt f n = true ↔ HasCollisionMarker f n := by
  simp only [markerAt, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · intro h j
    have hj := j.isLt
    have he : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 := by omega
    rcases he with he | he | he | he | he | he <;>
      simp only [he, collisionMarker, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, Nat.add_zero] <;> simp_all
  · intro h
    exact ⟨⟨⟨⟨⟨h ⟨0, by decide⟩, h ⟨1, by decide⟩⟩, h ⟨2, by decide⟩⟩,
      h ⟨3, by decide⟩⟩, h ⟨4, by decide⟩⟩, h ⟨5, by decide⟩⟩

def checkMarkerLocations (f : Nat -> Bool) (N : Nat) : Bool :=
  (List.range N).all (fun n => markerAt f n == (n == 107))

theorem checkMarkerLocations_sound {f : Nat -> Bool} {N : Nat}
    (h : checkMarkerLocations f N = true) (n : Nat) (hn : n < N) :
    HasCollisionMarker f n ↔ n = 107 := by
  have hh := (List.all_eq_true.mp h) n (List.mem_range.mpr hn)
  have he : markerAt f n = (n == 107) := by simpa only [beq_iff_eq] using hh
  rw [← markerAt_iff, he, beq_iff_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem collisionMarker_location_check :
    (checkMarkerLocations (spacedColor 0) 548 && checkMarkerLocations (spacedColor 1) 652 &&
      checkMarkerLocations certifiedColor 104) = true := by
  simp only [checkMarkerLocations, markerAt, spacedColor, obstacleColor_bits, certifiedColor_bits]
  decide +kernel

theorem collisionMarker_checks :
    (forall n : Fin 548, HasCollisionMarker (spacedColor 0) n.val ↔ n.val = 107) ∧
    (forall n : Fin 652, HasCollisionMarker (spacedColor 1) n.val ↔ n.val = 107) ∧
    (forall n : Fin 104, ¬HasCollisionMarker certifiedColor n.val) := by
  have h := collisionMarker_location_check
  simp only [Bool.and_eq_true] at h
  refine ⟨fun n => checkMarkerLocations_sound h.1.1 n.val n.isLt,
    fun n => checkMarkerLocations_sound h.1.2 n.val n.isLt, ?_⟩
  intro n hn
  have he := (checkMarkerLocations_sound h.2 n.val n.isLt).mp hn
  omega

end LangtonsAnt
