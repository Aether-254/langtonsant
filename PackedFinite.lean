import PackedAnt

namespace LangtonsAnt

def packCells : List Point -> Nat
  | [] => 0
  | p :: ps => packCells ps ||| (2 ^ bitIndex p)

theorem packedBoard_packCells (cells : List Point)
    (hbox : forall p, p ∈ cells -> InBox p) :
    packedBoard (packCells cells) = fun p => decide (p ∈ cells) := by
  induction cells with
  | nil => funext p; simp [packCells, packedBoard]
  | cons p ps ih =>
    have hp := hbox p (by simp)
    have ht := ih (fun q hq => hbox q (by simp [hq]))
    funext q
    by_cases hq : InBox q
    · have heq : bitIndex p = bitIndex q ↔ q = p :=
        ⟨fun h => (bitIndex_injective hp hq h).symm, fun h => by rw [h]⟩
      have hh := congrFun ht q
      simp only [packedBoard, ite_eq_left hq] at hh
      simp [packCells, packedBoard, hq, Nat.testBit_or, Nat.testBit_two_pow, heq, hh, Bool.or_comm]
    · have hn : q ∉ p :: ps := fun h => hq (hbox q h)
      simp [packedBoard, hq, hn]

def FiniteState.toPacked (s : FiniteState) : PackedState :=
  ⟨packCells s.black, s.pos, s.dir⟩

theorem FiniteState.toPacked_toState (s : FiniteState)
    (hbox : forall p, p ∈ s.black -> InBox p) : s.toPacked.toState = s.toState := by
  simp only [toPacked, PackedState.toState, toState, packedBoard_packCells s.black hbox]

def checkPackedBounded (cut : Int) : Nat -> PackedState -> Bool
  | 0, _ => true
  | n + 1, s => decide (InBox s.pos) && decide (weight s.pos <= cut) &&
      checkPackedBounded cut n s.step

theorem checkPackedBounded_sound {cut : Int} {n : Nat} {s : PackedState}
    (h : checkPackedBounded cut n s = true) :
    forall j, j < n -> weight (run s.toState j).pos <= cut := by
  induction n generalizing s with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [checkPackedBounded, Bool.and_eq_true, decide_eq_true_eq] at h
    intro j hj
    cases j with
    | zero => exact h.1.2
    | succ j =>
      have hh := ih h.2 j (by omega)
      rw [PackedState.toState_step _ h.1.1] at hh
      change weight (run (run s.toState 1) j).pos <= cut at hh
      rw [← run_add] at hh
      simpa only [Nat.add_comm 1 j] using hh

end LangtonsAnt
