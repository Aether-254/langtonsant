import FirstContact
import SeparatedInitialStates

namespace LangtonsAnt

def cellsMask (cells : List Point) : Board := fun p => decide (p ∈ cells)

def contactCycles (cells : List Point) : Nat := (-(weightFloor cells)).toNat + 1

/-- A safe, coordinate-dependent bound, not a bound on recovery after collision. -/
def contactBound (cells : List Point) : Nat := 12080 + 104 * contactCycles cells

theorem blank_tail_weight (k j : Nat) (hj : j < 104) :
    weight (run blank (12080 + (104 * k + j))).pos <= -86 - 4 * (k : Int) := by
  have hc := highwaySeed_certificate.translate (-56, -30)
  have hm := hc.block_prefix k j (by omega)
  have he : AgreesBelow (0 + weight (-56, -30)) (run blank 12080)
      (translate (-56, -30) highwaySeed.toState) := blank_entry
  have he' := hc.matches_forever he (104 * k + j)
  rw [← run_add] at he'
  rw [he'.pos, hm.pos]
  change weight (addPoint (offset (-2, -2) k)
    (run (translate (-56, -30) highwaySeed.toState) j).pos) <= _
  rw [weight_addPoint, southwest_offset]
  have hb := hc.bounded j hj
  simp only [weight] at hb ⊢
  omega

theorem blank_no_contact_after_bound (cells : List Point) {n : Nat}
    (hn : contactBound cells <= n) : (run blank n).pos ∉ cells := by
  intro hm
  let d := n - 12080
  let k := d / 104
  let j := d % 104
  have hdecomp : 104 * k + j = d := Nat.div_add_mod d 104
  have hj : j < 104 := Nat.mod_lt d (by decide)
  have hnk : contactCycles cells <= k := by
    unfold contactBound at hn
    dsimp [d, k] at *
    omega
  have hn' : n = 12080 + (104 * k + j) := by
    unfold contactBound at hn
    dsimp [d] at hdecomp
    omega
  have hb := blank_tail_weight k j hj
  rw [← hn'] at hb
  have hfloor := weightFloor_le hm
  unfold contactCycles at hnk
  omega

def searchContact (cells : List Point) : Nat -> FiniteState -> Option Nat
  | 0, _ => none
  | fuel + 1, s =>
    if s.pos ∈ cells then some 0 else
      (searchContact cells fuel s.step).map (fun n => n + 1)

theorem searchContact_none_iff (cells : List Point) (fuel : Nat) (s : FiniteState) :
    searchContact cells fuel s = none ↔
      forall j, j < fuel -> (run s.toState j).pos ∉ cells := by
  induction fuel generalizing s with
  | zero => simp [searchContact]
  | succ fuel ih =>
    by_cases hp : s.pos ∈ cells
    · constructor
      · intro h
        simp [searchContact, hp] at h
      · intro h
        exact False.elim (h 0 (by omega) hp)
    · have hshift : forall j, run s.step.toState j = run s.toState (j + 1) := by
        intro j
        rw [FiniteState.toState_step]
        change run (run s.toState 1) j = _
        rw [← run_add, Nat.add_comm 1 j]
      constructor
      · intro h
        have hh : searchContact cells fuel s.step = none := by simpa [searchContact, hp] using h
        have ht := (ih s.step).mp hh
        intro j hj
        cases j with
        | zero => exact hp
        | succ j => simpa only [hshift] using ht j (by omega)
      · intro h
        have ht : forall j, j < fuel -> (run s.step.toState j).pos ∉ cells := by
          intro j hj
          rw [hshift]
          exact h (j + 1) (by omega)
        simp [searchContact, hp, (ih s.step).mpr ht]

theorem searchContact_some_sound {cells : List Point} {fuel : Nat} {s : FiniteState} {T : Nat}
    (h : searchContact cells fuel s = some T) :
    T < fuel ∧ (run s.toState T).pos ∈ cells ∧
      forall j, j < T -> (run s.toState j).pos ∉ cells := by
  induction fuel generalizing s T with
  | zero => simp [searchContact] at h
  | succ fuel ih =>
    by_cases hp : s.pos ∈ cells
    · have heq : 0 = T := by simpa [searchContact, hp] using h
      subst T
      exact ⟨by omega, hp, by intro j hj; omega⟩
    · cases hr : searchContact cells fuel s.step with
      | none => simp [searchContact, hp, hr] at h
      | some k =>
        have heq : k + 1 = T := by simpa [searchContact, hp, hr] using h
        subst T
        have hk := ih hr
        have hshift : forall j, run s.step.toState j = run s.toState (j + 1) := by
          intro j
          rw [FiniteState.toState_step]
          change run (run s.toState 1) j = _
          rw [← run_add, Nat.add_comm 1 j]
        refine ⟨by omega, ?_, ?_⟩
        · simpa only [hshift] using hk.2.1
        · intro j hj
          cases j with
          | zero => exact hp
          | succ j => simpa only [hshift] using hk.2.2 j (by omega)

/-- This total classifier decides first contact with the blank reference path, not eventual recovery. -/
def decideBlankContact (cells : List Point) : Option Nat :=
  searchContact cells (contactBound cells) finiteBlank

theorem decideBlankContact_none_iff (cells : List Point) :
    decideBlankContact cells = none ↔
      forall n, cellsMask cells (run blank n).pos = false := by
  rw [decideBlankContact, searchContact_none_iff]
  simp only [finiteBlank_toState]
  constructor
  · intro h n
    have hn : (run blank n).pos ∉ cells := by
      by_cases hlt : n < contactBound cells
      · exact h n hlt
      · exact blank_no_contact_after_bound cells (by omega)
    simp [cellsMask, hn]
  · intro h n _
    simpa [cellsMask] using h n

theorem decideBlankContact_some_first {cells : List Point} {T : Nat}
    (h : decideBlankContact cells = some T) : FirstContact (cellsMask cells) blank T := by
  have hh := searchContact_some_sound h
  simp only [finiteBlank_toState] at hh
  refine ⟨by simpa [cellsMask] using hh.2.1, ?_⟩
  intro j hj
  simpa [cellsMask] using hh.2.2 j hj

theorem decideBlankContact_some_iff (cells : List Point) (T : Nat) :
    decideBlankContact cells = some T ↔ FirstContact (cellsMask cells) blank T := by
  constructor
  · exact decideBlankContact_some_first
  · intro hT
    cases hc : decideBlankContact cells with
    | none =>
      have hh := (decideBlankContact_none_iff cells).mp hc T
      rw [hT.1] at hh
      contradiction
    | some U =>
      have heq := (decideBlankContact_some_first hc).unique hT
      rw [heq]

theorem decideBlankContact_none_standard {cells : List Point}
    (h : decideBlankContact cells = none) :
    StandardHighwayFrom (perturb (cellsMask cells) blank) 12080 (-2, -2) :=
  perturb_standard_of_avoids blank_standard ((decideBlankContact_none_iff cells).mp h)

end LangtonsAnt
