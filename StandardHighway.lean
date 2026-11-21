import HighwayChecker

namespace LangtonsAnt

/-- An explicit 23-cell seed for the southwest standard highway, facing north. -/
def highwaySeed : FiniteState :=
  { black := [(-2, -1), (2, -2), (2, -3), (2, -4), (2, -6), (1, -1),
      (-1, -4), (3, -5), (1, -5), (0, -3), (0, -2), (1, -3), (4, -4),
      (1, -4), (-1, 0), (0, -5), (0, -1), (0, 0), (-1, 1), (-2, 0),
      (2, -5), (1, -6), (-1, -3)]
    pos := (0, 0)
    dir := .north }

theorem highwaySeed_size : highwaySeed.black.length = 23 := by decide

theorem highwaySeed_distinct : highwaySeed.black.Nodup := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem highwaySeed_check : checkCertificate highwaySeed 104 (-2, -2) 0 = true := by
  decide +kernel

theorem highwaySeed_certificate : HighwayCertificate highwaySeed.toState 104 (-2, -2) 0 :=
  checkCertificate_sound highwaySeed_check

theorem highwaySeed_highway : HighwayFrom highwaySeed.toState 0 104 (-2, -2) :=
  highwaySeed_certificate.highway

theorem highwaySeed_reads (n : Nat) :
    readColor highwaySeed.toState n = readColor highwaySeed.toState (n % 104) :=
  highwaySeed_certificate.reads n

theorem highwaySeed_finite : FiniteSupport highwaySeed.toState.board :=
  highwaySeed.finiteSupport

/-- A literal turn word certified against the seed, not assumed from a simulation. -/
def highwayWord : List Bool :=
  "LLRLRRRRLRLLLLRRRRLRRLRRRRLLLLRLRRRRLRRRRLLLLRLRRRRLRLLRRLLLLRRLLRRRRLLRRLRLLRLLRLRLLRRRRLLRLLRRRRLLRRRR".toList.map
    (fun c => c == 'L')

theorem highwayWord_length : highwayWord.length = 104 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem highwayWord_check : checkTrace highwaySeed highwayWord = true := by decide +kernel

def certifiedColor (n : Nat) : Bool := highwayWord[n % 104]?.getD false

theorem highwaySeed_exact_reads (n : Nat) :
    readColor highwaySeed.toState n = certifiedColor n := by
  rw [highwaySeed_reads]
  exact checkTrace_sound highwayWord_check (n % 104)
    (by rw [highwayWord_length]; exact Nat.mod_lt _ (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem highwayWord_no_short_period :
    forall q : Fin 104, 0 < q.val ->
      exists j : Fin 104, certifiedColor (j.val + q.val) ≠ certifiedColor j.val := by
  decide +kernel

/-- The read/turn sequence has no positive period shorter than 104. -/
theorem highwaySeed_minimal_read_period (q : Nat) (hq : 0 < q) (hsmall : q < 104) :
    ¬(forall n, readColor highwaySeed.toState (n + q) = readColor highwaySeed.toState n) := by
  intro h
  obtain ⟨j, hj⟩ := highwayWord_no_short_period ⟨q, hsmall⟩ hq
  have hh := h j.val
  simp only [highwaySeed_exact_reads] at hh
  exact hj hh

theorem highwaySeed_entry {s : State} {T : Nat}
    (h : AgreesBelow 0 (run s T) highwaySeed.toState) :
    HighwayFrom s T 104 (-2, -2) :=
  highwaySeed_certificate.highway_of_entry h

theorem highwaySeed_translated_entry {s : State} {T : Nat} (origin : Point)
    (h : AgreesBelow (weight origin) (run s T) (translate origin highwaySeed.toState)) :
    HighwayFrom s T 104 (-2, -2) := by
  apply (highwaySeed_certificate.translate origin).highway_of_entry
  simpa only [Int.zero_add] using h

end LangtonsAnt
