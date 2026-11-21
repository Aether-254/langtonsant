import PackedAnt
import StandardHighway

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem blank_reference_check :
    checkPackedTraceAfter 10000 packedBlank highwayWord = true := by
  decide +kernel

theorem standardColor_eq_certifiedColor (n : Nat) : standardColor n = certifiedColor n := by
  have h := checkPackedTraceAfter_sound blank_reference_check (n % 104)
    (by rw [highwayWord_length]; exact Nat.mod_lt _ (by decide))
  simpa only [packedBlank_toState, standardColor, certifiedColor] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem blank_entry_check :
    checkPackedEntry 12080 packedBlank (-86) (highwaySeed.translate (-56, -30)) = true := by
  decide +kernel

theorem blank_entry :
    AgreesBelow (-86) (run blank 12080) (translate (-56, -30) highwaySeed.toState) := by
  have h := checkPackedEntry_sound blank_entry_check
  simpa only [packedBlank_toState, FiniteState.toState_translate] using h

theorem blank_highway : HighwayFrom blank 12080 104 (-2, -2) := by
  apply highwaySeed_translated_entry (-56, -30)
  rw [show weight ((-56, -30) : Point) = -86 by decide]
  exact blank_entry

theorem highwaySeed_standard : StandardHighwayFrom highwaySeed.toState 0 (-2, -2) := by
  refine ⟨highwaySeed_highway, ?_⟩
  intro n
  simpa only [Nat.zero_add, standardColor_eq_certifiedColor] using highwaySeed_exact_reads n

theorem blank_standard : StandardHighwayFrom blank 12080 (-2, -2) := by
  refine ⟨blank_highway, ?_⟩
  intro n
  have hentry : AgreesBelow (0 + weight (-56, -30)) (run blank 12080)
      (translate (-56, -30) highwaySeed.toState) := blank_entry
  have hr := (highwaySeed_certificate.translate (-56, -30)).reads_of_matches hentry n
  rw [translate_readColor] at hr
  have hmod := highwaySeed_exact_reads (n % 104)
  simp only [certifiedColor, Nat.mod_mod] at hmod
  have hh := hr.trans hmod
  simpa only [readColor, ← run_add, standardColor_eq_certifiedColor, certifiedColor] using hh

/-- A fully explicit sufficient condition, with arbitrary history outside the half-plane. -/
theorem standard_highway_of_entry {s : State} {T : Nat} (origin : Point)
    (h : AgreesBelow (weight origin) (run s T) (translate origin highwaySeed.toState)) :
    StandardHighwayFrom s T (-2, -2) := by
  refine ⟨highwaySeed_translated_entry origin h, ?_⟩
  intro n
  have hh : AgreesBelow (0 + weight origin) (run s T)
      (translate origin highwaySeed.toState) := by simpa only [Int.zero_add] using h
  have hr := (highwaySeed_certificate.translate origin).reads_of_matches hh n
  rw [translate_readColor, highwaySeed_exact_reads] at hr
  simpa only [readColor, ← run_add, standardColor_eq_certifiedColor,
    certifiedColor, Nat.mod_mod] using hr

theorem blank_minimal_read_period (q : Nat) (hq : 0 < q) (hsmall : q < 104) :
    ¬(forall n, readColor blank (12080 + n + q) = readColor blank (12080 + n)) := by
  intro h
  apply highwaySeed_minimal_read_period q hq hsmall
  intro n
  have hh := h n
  rw [Nat.add_assoc, blank_standard.2 (n + q), blank_standard.2 n] at hh
  simpa only [standardColor_eq_certifiedColor, ← highwaySeed_exact_reads] using hh

end LangtonsAnt
