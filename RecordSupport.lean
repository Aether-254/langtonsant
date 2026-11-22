import RecordPair

namespace LangtonsAnt

/-- A black cell initially white has a most recent white read, with no intervening visit. -/
theorem black_has_white_source (s : State) (p : Point) (n : Nat) (hinit : s.board p = false)
    (hblack : (run s n).board p = true) :
    exists j, j < n ∧ (run s j).pos = p ∧ readColor s j = false ∧
      forall r, j < r -> r < n -> (run s r).pos ≠ p := by
  induction n with
  | zero => simp only [run_zero] at hblack; rw [hinit] at hblack; contradiction
  | succ n ih =>
    change flip (run s n).board (run s n).pos p = true at hblack
    by_cases hp : (run s n).pos = p
    · rw [hp, flip_same] at hblack
      refine ⟨n, by omega, hp, ?_, ?_⟩
      · unfold readColor
        rw [hp]
        cases hc : (run s n).board p <;> simp_all
      · intro r hr hn; omega
    · rw [flip_other _ (Ne.symm hp)] at hblack
      obtain ⟨j, hj, hpos, hc, hgap⟩ := ih hblack
      refine ⟨j, by omega, hpos, hc, ?_⟩
      intro r hr hn
      by_cases he : r = n
      · simpa only [he] using hp
      · exact hgap r hr (by omega)

def RunRecord (s1 s2 : Int) (s : State) (n : Nat) : Prop :=
  forall k, k < n -> linearForm s1 s2 (run s k).pos < linearForm s1 s2 (run s n).pos

theorem finiteSupport_white_above {s : State} (hs : FiniteSupport s.board) (s1 s2 : Int) :
    exists bound : Int, forall p, bound < linearForm s1 s2 p -> s.board p = false := by
  obtain ⟨cells, hc⟩ := hs
  let values := 0 :: cells.map (linearForm s1 s2)
  have hne : values ≠ [] := by simp [values]
  refine ⟨values.max hne, ?_⟩
  intro p hp
  cases he : s.board p with
  | false => rfl
  | true =>
    have hmem : linearForm s1 s2 p ∈ values :=
      List.mem_cons_of_mem 0 (List.mem_map.mpr ⟨p, hc p he, rfl⟩)
    have hh := List.le_max_of_mem hmem
    omega

theorem run_level_succ (s1 s2 : Int) (s : State) (n : Nat) :
    linearForm s1 s2 (run s (n + 1)).pos = linearForm s1 s2 (run s n).pos +
      gain s1 s2 (turn (readColor s n) (run s n).dir) := by
  exact linearForm_move_gain _ _ _ _

private theorem support_heading_unique {s1 s2 : Int} {d e : Direction}
    (haxis : e.horizontal = d.horizontal)
    (hd : gain s1 s2 (turn true d) = 1) (he : gain s1 s2 (turn false e) = -1) : e = d := by
  cases d <;> cases e <;>
    simp [Direction.horizontal, gain, turn, Direction.right, Direction.left] at haxis hd he ⊢ <;> omega

/-- A white read supporting the black turn into a new record has exactly the same pose.
The supporting excursion stays behind the old frontier. -/
theorem record_support_pose {s1 s2 : Int} (hs1 : UnitSign s1) (hs2 : UnitSign s2)
    (s : State) {j m : Nat} (hj : j < m) (hp : (run s j).pos = (run s m).pos)
    (hw : readColor s j = false) (hb : readColor s m = true)
    (hr : RunRecord s1 s2 s (m + 1)) :
    (run s j).dir = (run s m).dir ∧
      forall k, k <= m -> linearForm s1 s2 (run s k).pos <= linearForm s1 s2 (run s m).pos := by
  have hm := run_level_succ s1 s2 s m
  rw [hb] at hm
  have hcurrent := hr m (by omega)
  have hgm : gain s1 s2 (turn true (run s m).dir) = 1 := by
    have hg := gain_unit hs1 hs2 (turn true (run s m).dir)
    omega
  rw [hgm] at hm
  have hprevious := hr (j + 1) (by omega)
  have hjstep := run_level_succ s1 s2 s j
  rw [hw, hp] at hjstep
  have hgj : gain s1 s2 (turn false (run s j).dir) = -1 := by
    have hg := gain_unit hs1 hs2 (turn false (run s j).dir)
    omega
  refine ⟨support_heading_unique (same_cell_same_axis s hp) hgm hgj, ?_⟩
  intro k hk
  have hh := hr k (by omega)
  omega

/-- The missing antecedent in a bare front-factor test: the preceding black read must
be backed by a genuine closed-pose, first-return excursion if that cell was initially white. -/
theorem record_black_has_support_excursion {s1 s2 : Int}
    (hs1 : UnitSign s1) (hs2 : UnitSign s2) (s : State) (m : Nat)
    (hinit : s.board (run s m).pos = false) (hb : readColor s m = true)
    (hr : RunRecord s1 s2 s (m + 1)) :
    exists j, j < m ∧ (run s j).pos = (run s m).pos ∧
      (run s j).dir = (run s m).dir ∧ readColor s j = false ∧
      (forall r, j < r -> r < m -> (run s r).pos ≠ (run s m).pos) ∧
      forall k, j <= k -> k <= m ->
        linearForm s1 s2 (run s k).pos <= linearForm s1 s2 (run s m).pos := by
  obtain ⟨j, hj, hp, hw, hgap⟩ := black_has_white_source s (run s m).pos m hinit hb
  obtain ⟨hd, hbound⟩ := record_support_pose hs1 hs2 s hj hp hw hb hr
  exact ⟨j, hj, hp, hd, hw, hgap, fun k _ hk => hbound k hk⟩

/-- The step before a strict record attains the previous maximum. -/
theorem record_predecessor_max {s1 s2 : Int} (hs1 : UnitSign s1) (hs2 : UnitSign s2)
    (s : State) (m : Nat) (hr : RunRecord s1 s2 s (m + 1)) :
    linearForm s1 s2 (run s (m + 1)).pos = linearForm s1 s2 (run s m).pos + 1 ∧
      forall k, k <= m -> linearForm s1 s2 (run s k).pos <= linearForm s1 s2 (run s m).pos := by
  have hm := run_level_succ s1 s2 s m
  have hc := hr m (by omega)
  have hg := gain_unit hs1 hs2 (turn (readColor s m) (run s m).dir)
  have he : gain s1 s2 (turn (readColor s m) (run s m).dir) = 1 := by omega
  rw [he] at hm
  refine ⟨hm, ?_⟩
  intro k hk
  have hh := hr k (by omega)
  omega

/-- Positive-time arrivals at a future record's base must have the same heading. -/
theorem record_base_heading {s1 s2 : Int} (hs1 : UnitSign s1) (hs2 : UnitSign s2)
    (s : State) {t m : Nat} (ht : 0 < t) (htm : t <= m)
    (hp : (run s t).pos = (run s m).pos) (hr : RunRecord s1 s2 s (m + 1)) :
    (run s t).dir = (run s m).dir := by
  have hmax := (record_predecessor_max hs1 hs2 s m hr).2
  have arriving (k : Nat) (hk : 0 < k) (hkm : k <= m)
      (hpos : (run s k).pos = (run s m).pos) : gain s1 s2 (run s k).dir = 1 := by
    cases k with
    | zero => omega
    | succ r =>
      have he : linearForm s1 s2 (run s (r + 1)).pos = linearForm s1 s2 (run s r).pos +
          gain s1 s2 (run s (r + 1)).dir := linearForm_move_gain _ _ _ _
      rw [hpos] at he
      have hh := hmax r (by omega)
      have hg := gain_unit hs1 hs2 (run s (r + 1)).dir
      omega
  exact gain_unique hs1 hs2 (same_cell_same_axis s hp)
    (arriving t ht htm hp) (arriving m (by omega) (by omega) rfl)

/-- Every earlier read at an initially white record base is white. A black read would
already have left through the as-yet unvisited next level. -/
theorem record_base_prior_white {s1 s2 : Int} (hs1 : UnitSign s1) (hs2 : UnitSign s2)
    (s : State) {t m : Nat} (ht : t < m) (hp : (run s t).pos = (run s m).pos)
    (hinit : s.board (run s m).pos = false) (hb : readColor s m = true)
    (hr : RunRecord s1 s2 s (m + 1)) : readColor s t = false := by
  by_cases hz : t = 0
  · subst t
    change s.board (run s 0).pos = false
    rw [hp]
    exact hinit
  · have hd := record_base_heading hs1 hs2 s (by omega : 0 < t) (by omega) hp hr
    cases hc : readColor s t with
    | false => rfl
    | true =>
      have a := run_level_succ s1 s2 s t
      have b := run_level_succ s1 s2 s m
      rw [hc, hd, hp] at a
      rw [hb] at b
      have hh := hr (t + 1) (by omega)
      omega

/-- If all earlier visits would read white, a cell still white has not been visited. -/
theorem white_reads_final_white_no_visit (s : State) (p : Point) (n : Nat) :
    (forall j, j < n -> (run s j).pos = p -> readColor s j = false) ->
    (run s n).board p = false -> forall j, j < n -> (run s j).pos ≠ p := by
  induction n with
  | zero => intro _ _ j hj; omega
  | succ n ih =>
    intro hw hf
    change flip (run s n).board (run s n).pos p = false at hf
    by_cases hp : (run s n).pos = p
    · have hc := hw n (by omega) hp
      change (run s n).board (run s n).pos = false at hc
      rw [hp] at hc
      rw [hp, flip_same, hc] at hf
      contradiction
    · rw [flip_other _ (Ne.symm hp)] at hf
      have hprev := ih (fun j hj he => hw j (by omega) he) hf
      intro j hj
      by_cases he : j = n
      · simpa only [he] using hp
      · exact hprev j (by omega)

/-- A black turn into a new record is the SECOND visit to its initially white base.
The unique earlier visit is a white read at the same pose. -/
theorem record_black_has_first_return {s1 s2 : Int}
    (hs1 : UnitSign s1) (hs2 : UnitSign s2) (s : State) (m : Nat)
    (hinit : s.board (run s m).pos = false) (hb : readColor s m = true)
    (hr : RunRecord s1 s2 s (m + 1)) :
    exists j, j < m ∧ (run s j).pos = (run s m).pos ∧
      (run s j).dir = (run s m).dir ∧ readColor s j = false ∧
      (forall r, r < m -> ((run s r).pos = (run s m).pos ↔ r = j)) ∧
      forall k, k <= m ->
        linearForm s1 s2 (run s k).pos <= linearForm s1 s2 (run s m).pos := by
  obtain ⟨j, hj, hp, hw, hgap⟩ := black_has_white_source s (run s m).pos m hinit hb
  obtain ⟨hd, hbound⟩ := record_support_pose hs1 hs2 s hj hp hw hb hr
  have hfirst := white_reads_final_white_no_visit s (run s m).pos j
    (fun r hr' he => record_base_prior_white hs1 hs2 s (by omega) he hinit hb hr)
    (by simpa only [readColor, hp] using hw)
  refine ⟨j, hj, hp, hd, hw, ?_, hbound⟩
  intro r hrm
  constructor
  · intro he
    by_cases hl : r < j
    · exact False.elim (hfirst r hl he)
    · by_cases hg : j < r
      · exact False.elim (hgap r hg hrm he)
      · omega
  · intro he
    simpa only [he] using hp

/-- Support intervals from the SAME front are temporally disjoint. This makes no claim
about intervals belonging to different diagonal fronts. -/
theorem same_front_sources_ordered {s1 s2 : Int} (hs1 : UnitSign s1) (hs2 : UnitSign s2)
    (s : State) {j m n : Nat} (hmn : m < n)
    (hm : RunRecord s1 s2 s (m + 1)) (hn : RunRecord s1 s2 s (n + 1))
    (hp : (run s j).pos = (run s n).pos) : m < j := by
  have hh := (record_predecessor_max hs1 hs2 s n hn).2 (m + 1) (by omega)
  by_cases h : m < j
  · exact h
  · have hprev := hm j (by omega)
    rw [hp] at hprev
    omega

end LangtonsAnt
