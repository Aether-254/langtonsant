import RecordSupport

namespace LangtonsAnt

namespace RecordSupportExamples

def prefixWord : List Bool :=
  "RRRRLRRRRLRRRRLLLLRLRRRRLRRRRLLLLRLRRRRLRRRRLLLLRLLRRLRRRRLLLLRLRRRRLRRRRLLLLRLR".toList.map
    (fun c => c == 'L')

def prefixColor (n : Nat) : Bool := prefixWord[n]?.getD false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem prefix_checked : packedTrace packedBlank prefixWord = true := by decide +kernel

theorem blank_color {n : Nat} (hn : n < 80) : readColor blank n = prefixColor n := by
  simpa only [prefixColor, packedBlank_toState] using packedTrace_sound prefix_checked n (by
    have he : prefixWord.length = 80 := by decide +kernel
    omega)

theorem blank_trace {n : Nat} (hn : n <= 80) :
    wordTrace prefixColor n = ((run blank n).pos, (run blank n).dir) := by
  have he : wordTrace prefixColor n = wordTrace (readColor blank) n :=
    wordTrace_congr (fun i hi => (blank_color (by omega : i < 80)).symm)
  exact he.trans (wordTrace_reads rfl rfl n)

private theorem blank_pos {n : Nat} (hn : n <= 80) :
    (run blank n).pos = wordPos prefixColor n := (congrArg Prod.fst (blank_trace hn)).symm

def prefixRecord (s1 s2 : Int) (n : Nat) : Prop :=
  forall k : Fin n, linearForm s1 s2 (wordPos prefixColor k) <
    linearForm s1 s2 (wordPos prefixColor n)

theorem prefixRecord_sound {s1 s2 : Int} {n : Nat} (hn : n <= 80)
    (h : prefixRecord s1 s2 n) : RunRecord s1 s2 blank n := by
  intro k hk
  rw [blank_pos hn, blank_pos (by omega : k <= 80)]
  exact h ⟨k, hk⟩

def FirstSupportAt (s : State) (j m : Nat) : Prop :=
  j < m ∧ (run s j).pos = (run s m).pos ∧ (run s j).dir = (run s m).dir ∧
    readColor s j = false ∧ readColor s m = true ∧
    forall r, r < m -> ((run s r).pos = (run s m).pos ↔ r = j)

theorem firstSupportAt_of_source {s1 s2 : Int} (hs1 : UnitSign s1) (hs2 : UnitSign s2)
    (s : State) (j m : Nat) (hinit : s.board (run s m).pos = false)
    (hb : readColor s m = true) (hr : RunRecord s1 s2 s (m + 1))
    (hj : j < m) (hp : (run s j).pos = (run s m).pos) : FirstSupportAt s j m := by
  obtain ⟨k, hk, hpos, hdir, hwhite, huniq, _⟩ :=
    record_black_has_first_return hs1 hs2 s m hinit hb hr
  have he : j = k := (huniq j hj).mp hp
  subst j
  exact ⟨hk, hpos, hdir, hwhite, hb, huniq⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem blank_records :
    RunRecord (-1) 1 blank 5 ∧ RunRecord 1 1 blank 54 ∧ RunRecord (-1) 1 blank 79 := by
  have a : prefixRecord (-1) 1 5 := by unfold prefixRecord; decide +kernel
  have b : prefixRecord 1 1 54 := by unfold prefixRecord; decide +kernel
  have c : prefixRecord (-1) 1 79 := by unfold prefixRecord; decide +kernel
  exact ⟨prefixRecord_sound (by decide) a, prefixRecord_sound (by decide) b,
    prefixRecord_sound (by decide) c⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem blank_sources :
    FirstSupportAt blank 0 4 ∧ FirstSupportAt blank 1 53 ∧ FirstSupportAt blank 70 78 := by
  have hp :
      wordPos prefixColor 0 = wordPos prefixColor 4 ∧
      wordPos prefixColor 1 = wordPos prefixColor 53 ∧
      wordPos prefixColor 70 = wordPos prefixColor 78 := by decide +kernel
  have hb : prefixColor 4 = true ∧ prefixColor 53 = true ∧ prefixColor 78 = true := by
    decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · exact firstSupportAt_of_source (Or.inr rfl : UnitSign (-1)) (Or.inl rfl : UnitSign 1)
      blank 0 4 rfl (by rw [blank_color (by decide)]; exact hb.1) blank_records.1 (by decide)
      (by rw [blank_pos (by decide), blank_pos (by decide)]; exact hp.1)
  · exact firstSupportAt_of_source (Or.inl rfl : UnitSign 1) (Or.inl rfl : UnitSign 1)
      blank 1 53 rfl (by rw [blank_color (by decide)]; exact hb.2.1) blank_records.2.1 (by decide)
      (by rw [blank_pos (by decide), blank_pos (by decide)]; exact hp.2.1)
  · exact firstSupportAt_of_source (Or.inr rfl : UnitSign (-1)) (Or.inl rfl : UnitSign 1)
      blank 70 78 rfl (by rw [blank_color (by decide)]; exact hb.2.2) blank_records.2.2 (by decide)
      (by rw [blank_pos (by decide), blank_pos (by decide)]; exact hp.2.2)

/-- The two genuine support intervals properly cross: 0 < 1 < 4 < 53.
This excludes a laminarity rule for arbitrary finite-support trajectories. -/
theorem crossing_distinct_fronts :
    FirstSupportAt blank 0 4 ∧ RunRecord (-1) 1 blank 5 ∧
    FirstSupportAt blank 1 53 ∧ RunRecord 1 1 blank 54 ∧
    (0 : Nat) < 1 ∧ (1 : Nat) < 4 ∧ (4 : Nat) < 53 := by
  exact ⟨blank_sources.1, blank_records.1, blank_sources.2.1, blank_records.2.1,
    by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem blank_front_pause (n : Nat) (hlo : 6 < n) (hhi : n < 79) :
    ¬ RunRecord (-1) 1 blank n := by
  have hb : forall r : Fin 79, linearForm (-1) 1 (wordPos prefixColor r) <= 2 := by
    decide +kernel
  have h6 : linearForm (-1) 1 (wordPos prefixColor 6) = 2 := by decide +kernel
  intro h
  have hh := h 6 hlo
  rw [blank_pos (by decide : 6 <= 80), blank_pos (by omega : n <= 80), h6] at hh
  have hn := hb ⟨n, hhi⟩
  change linearForm (-1) 1 (wordPos prefixColor n) <= 2 at hn
  omega

/-- Successive record PAIRS need not use the preceding pair's second record as source.
For this front the pair starts are 5 and 79, but the second source is 70, not 6. -/
theorem source_link_fails :
    FirstSupportAt blank 0 4 ∧ FirstSupportAt blank 70 78 ∧
    RunRecord (-1) 1 blank 5 ∧ RunRecord (-1) 1 blank 6 ∧ RunRecord (-1) 1 blank 79 ∧
    RunRecord (-1) 1 blank 80 ∧
    (forall n, 6 < n -> n < 79 -> ¬ RunRecord (-1) 1 blank n) ∧
    (70 : Nat) ≠ 4 + 2 := by
  have h6 : prefixRecord (-1) 1 6 := by unfold prefixRecord; decide +kernel
  have h80 : prefixRecord (-1) 1 80 := by unfold prefixRecord; decide +kernel
  exact ⟨blank_sources.1, blank_sources.2.2, blank_records.1, prefixRecord_sound (by decide) h6,
    blank_records.2.2, prefixRecord_sound (by decide) h80, blank_front_pause, by decide⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem standard_sources :
    priorPhases 104 certifiedColor 21 = [33] ∧ priorPhases 104 certifiedColor 31 = [23] ∧
    wordPos certifiedColor 33 = addPoint (wordPos certifiedColor 21) (-2, -2) ∧
    wordPos certifiedColor 23 = wordPos certifiedColor 31 := by
  decide +kernel

end RecordSupportExamples

end LangtonsAnt
