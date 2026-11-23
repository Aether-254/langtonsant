import DiagonalRankZeroLane

/-!
# Winding across the occupied top layer

The upper bridge joins adjacent first-inner lanes by an east step followed by
a south step. Its displacement is `(1, -1)`, not a physical return.
-/

namespace LangtonsAnt.DiagonalWinding

open DiagonalMultipleLanes DiagonalRankZeroLane

private def travelSlack (w : Nat -> Bool) (i : Nat) : Int :=
  (i : Int) - ((wordPos w i).1 - (wordPos w i).2)

private theorem travelSlack_step (w : Nat -> Bool) (i : Nat) :
    travelSlack w i <= travelSlack w (i + 1) := by
  unfold travelSlack
  change (i : Int) - ((wordPos w i).1 - (wordPos w i).2) <=
    ((i + 1 : Nat) : Int) -
      ((move (wordPos w i) (outDir w i)).1 - (move (wordPos w i) (outDir w i)).2)
  cases outDir w i <;> simp only [move] <;> omega

private theorem travelSlack_mono (w : Nat -> Bool) {i j : Nat} (hij : i <= j) :
    travelSlack w i <= travelSlack w j := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact Int.le_refl _
  | succ j ih =>
    by_cases h : i <= j
    · exact Int.le_trans (ih h) (travelSlack_step w j)
    · have hi : i = j + 1 := by omega
      subst i
      exact Int.le_refl _

/-- A bottom-layer north departure gives a positive displacement deficit.
This bound does not require occupancy of the top layer. -/
theorem strict_period_bound {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = diagDrift m) :
    2 * m < P := by
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; exact layer_diagDrift m
  obtain ⟨i, hi, hbot⟩ := exists_botLayer_phase (w := w) h.pos_period
  have hn := (TwoCellDiagonal.botLayer_phase_rigid_of_layer_zero h hlv hi hbot).2.2.2.1
  have hbefore := travelSlack_mono w (show 0 <= i by omega)
  have hafter := travelSlack_mono w (show i + 1 <= P by omega)
  have hstep : travelSlack w (i + 1) = travelSlack w i + 2 := by
    unfold travelSlack
    change ((i + 1 : Nat) : Int) -
      ((move (wordPos w i) (outDir w i)).1 - (move (wordPos w i) (outDir w i)).2) = _
    rw [hn]
    simp only [move]
    omega
  have hzero : travelSlack w 0 = 0 := rfl
  have hend : travelSlack w P = (P : Int) - 2 * (m : Int) := by
    unfold travelSlack
    change (P : Int) - ((wordDrift P w).1 - (wordDrift P w).2) = _
    rw [hd]
    simp only [diagDrift]
    omega
  omega

/-- The upper arrival rank in any of the four first-inner candidate words. -/
def upperArrivalRank (a : List Bool) : Nat := if a.headD false then 0 else 2

/-- The upper departure rank in any of the four first-inner candidate words. -/
def upperDepartureRank (a : List Bool) : Nat := if a.headD false then 2 else 0

def upperArrival (m P : Nat) (w : Nat -> Bool) (r : Int) : Nat :=
  classPhaseAtRank (diagDrift m) P w (laneCell (topLayer P w - 1) r)
    (upperArrivalRank (laneAlpha m P w (topLayer P w - 1) r))

def upperDeparture (m P : Nat) (w : Nat -> Bool) (r : Int) : Nat :=
  classPhaseAtRank (diagDrift m) P w (laneCell (topLayer P w - 1) r)
    (upperDepartureRank (laneAlpha m P w (topLayer P w - 1) r))

theorem first_inner_length_gt_two {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Int) :
    2 < (Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w - 1) r)).length := by
  have hl := classPortWord_length (diagDrift m) P w (laneCell (topLayer P w - 1) r)
    (LangtonsAnt.alpha w)
  change (laneAlpha m P w (topLayer P w - 1) r).length = _ at hl
  rcases first_inner_candidates h hm hd ht r with ha | ha | ha | ha <;>
    rw [ha] at hl <;> simp only [word100, word1000, word001, word0010,
      List.length_cons, List.length_nil] at hl <;> omega

theorem upper_port_rank_lists {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Int) :
    UnitDiagonal.trueIdx (laneAlpha m P w (topLayer P w - 1) r) =
      [upperArrivalRank (laneAlpha m P w (topLayer P w - 1) r)] /\
    UnitDiagonal.trueIdx (laneBeta m P w (topLayer P w - 1) r) =
      [upperDepartureRank (laneAlpha m P w (topLayer P w - 1) r)] := by
  rw [laneBeta_depth1 h hm hd r]
  rcases first_inner_candidates h hm hd ht r with ha | ha | ha | ha <;> rw [ha] <;>
    exact ⟨rfl, rfl⟩

theorem upperArrival_mem {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Int) :
    upperArrival m P w r ∈ Drift.classPhases (diagDrift m) P w
      (laneCell (topLayer P w - 1) r) := by
  have hl := first_inner_length_gt_two h hm hd ht r
  apply classPhaseAtRank_mem hd (diagDrift_ne_zero hm)
  unfold upperArrivalRank
  split <;> omega

theorem upperDeparture_mem {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Int) :
    upperDeparture m P w r ∈ Drift.classPhases (diagDrift m) P w
      (laneCell (topLayer P w - 1) r) := by
  have hl := first_inner_length_gt_two h hm hd ht r
  apply classPhaseAtRank_mem hd (diagDrift_ne_zero hm)
  unfold upperDepartureRank
  split <;> omega

private theorem unique_phase_of_singleton_port {v c : Point} {P k : Nat}
    {w : Nat -> Bool} (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (f : Nat -> Bool) (hidx : UnitDiagonal.trueIdx (classPortWord v P w c f) = [k]) :
    classPhaseAtRank v P w c k ∈ Drift.classPhases v P w c /\
    f (classPhaseAtRank v P w c k) = true /\
    ∀ i ∈ Drift.classPhases v P w c, f i = true -> i = classPhaseAtRank v P w c k := by
  have hget : (classPortWord v P w c f)[k]? = some true :=
    UnitDiagonal.mem_trueIdx.mp (by rw [hidx]; simp)
  have hk : k < (Drift.classPhases v P w c).length := by
    simpa only [classPortWord_length] using UnitDiagonal.lt_length_of_getElem? hget
  refine ⟨classPhaseAtRank_mem hd hv hk, ?_, ?_⟩
  · rw [classPortWord_getElem? f hk] at hget
    exact Option.some.inj hget
  · intro i hi hf
    have hp := classPortWord_at_phase hd hv hi f
    rw [hf] at hp
    have hr := UnitDiagonal.mem_trueIdx.mpr hp
    rw [hidx, List.mem_singleton] at hr
    rw [← hr]
    exact (classPhaseAtRank_eq hd hv hi).symm

/-- The selected phase is the unique south arrival in the first-inner class. -/
theorem upperArrival_spec {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Int) :
    upperArrival m P w r ∈ Drift.arrivals (diagDrift m) P w
      (laneCell (topLayer P w - 1) r) .south /\
    ∀ i ∈ Drift.arrivals (diagDrift m) P w (laneCell (topLayer P w - 1) r) .south,
      i = upperArrival m P w r := by
  have hw : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 1) r)
      (fun i => decide (inDir w i = .south)) = laneAlpha m P w (topLayer P w - 1) r :=
    lane_incoming_portWord h hm hd 1 r true
  obtain ⟨hmem, hdir, huniq⟩ := unique_phase_of_singleton_port hd (diagDrift_ne_zero hm)
    (fun i => decide (inDir w i = .south)) (by rw [hw]; exact (upper_port_rank_lists h hm hd ht r).1)
  refine ⟨Drift.mem_arrivals.mpr ⟨(Drift.mem_classPhases.mp hmem).1,
    (Drift.mem_classPhases.mp hmem).2, of_decide_eq_true hdir⟩, ?_⟩
  intro i hi
  obtain ⟨hiP, hic, hid⟩ := Drift.mem_arrivals.mp hi
  exact huniq i (Drift.mem_classPhases.mpr ⟨hiP, hic⟩) (decide_eq_true hid)

/-- The selected phase is the unique east departure in the first-inner class. -/
theorem upperDeparture_spec {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Int) :
    upperDeparture m P w r ∈ Drift.departures (diagDrift m) P w
      (laneCell (topLayer P w - 1) r) .east /\
    ∀ i ∈ Drift.departures (diagDrift m) P w (laneCell (topLayer P w - 1) r) .east,
      i = upperDeparture m P w r := by
  have hw : classPortWord (diagDrift m) P w (laneCell (topLayer P w - 1) r)
      (fun i => decide (outDir w i = .east)) = laneBeta m P w (topLayer P w - 1) r :=
    lane_outgoing_portWord h hm hd 1 r true
  obtain ⟨hmem, hdir, huniq⟩ := unique_phase_of_singleton_port hd (diagDrift_ne_zero hm)
    (fun i => decide (outDir w i = .east)) (by rw [hw]; exact (upper_port_rank_lists h hm hd ht r).2)
  refine ⟨Drift.mem_departures.mpr ⟨(Drift.mem_classPhases.mp hmem).1,
    (Drift.mem_classPhases.mp hmem).2, of_decide_eq_true hdir⟩, ?_⟩
  intro i hi
  obtain ⟨hiP, hic, hid⟩ := Drift.mem_departures.mp hi
  exact huniq i (Drift.mem_classPhases.mpr ⟨hiP, hic⟩) (decide_eq_true hid)

/-- The actual two successive edges are E and S and reach the next lane's
unique upper arrival. The intermediate phase lies in the top class. -/
theorem upper_bridge {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Int) :
    let b := upperDeparture m P w r
    let t := Drift.succ P b
    outDir w b = .east /\
    t ∈ Drift.classPhases (diagDrift m) P w (laneCell (topLayer P w) (r + 1)) /\
    outDir w t = .south /\
    Drift.succ P t = upperArrival m P w (r + 1) := by
  intro b t
  have hlv : layer (wordDrift P w) = 0 := by rw [hd]; exact layer_diagDrift m
  have hbdep := (upperDeparture_spec h hm hd ht r).1
  obtain ⟨hbP, _, hbdir⟩ := Drift.mem_departures.mp hbdep
  have hmAT : Drift.SameClass (diagDrift m)
      (move (laneCell (topLayer P w - 1) r) .east) (laneCell (topLayer P w) (r + 1)) := by
    rw [move_laneCell_east, show topLayer P w - 1 + 1 = topLayer P w by omega]
    exact Drift.SameClass.refl _ _
  have htarr : t ∈ Drift.arrivals (diagDrift m) P w
      (laneCell (topLayer P w) (r + 1)) .east := by
    have hs := (Drift.successor_mem_iff h.1 hd hbP).mpr hbdep
    rwa [Drift.arrivals_congr P w .east hmAT] at hs
  obtain ⟨htP, htc, _⟩ := Drift.mem_arrivals.mp htarr
  have httop : layer (wordPos w t) = topLayer P w :=
    (TwoCellDiagonal.layer_eq_of_sameClass (layer_diagDrift m) htc).trans (layer_laneCell _ _)
  have htdir : outDir w t = .south :=
    (TwoCellDiagonal.topLayer_phase_rigid_of_layer_zero h hlv htP httop).2.2.2.1
  have htdep : t ∈ Drift.departures (diagDrift m) P w
      (laneCell (topLayer P w) (r + 1)) .south := Drift.mem_departures.mpr ⟨htP, htc, htdir⟩
  have haarr : Drift.succ P t ∈ Drift.arrivals (diagDrift m) P w
      (laneCell (topLayer P w - 1) (r + 1)) .south := by
    have hs := (Drift.successor_mem_iff h.1 hd htP).mpr htdep
    rwa [move_laneCell_south] at hs
  exact ⟨hbdir, Drift.mem_classPhases.mpr ⟨htP, htc⟩, htdir,
    (upperArrival_spec h hm hd ht (r + 1)).2 _ haarr⟩

theorem upperArrival_periodic (m P : Nat) (w : Nat -> Bool) (r : Int) :
    upperArrival m P w (r + (m : Int)) = upperArrival m P w r := by
  unfold upperArrival
  rw [laneAlpha_periodic]
  exact (classPhaseAtRank_congr P w _ (sameClass_laneCell_add_m m _ r)).symm

theorem upperDeparture_periodic (m P : Nat) (w : Nat -> Bool) (r : Int) :
    upperDeparture m P w (r + (m : Int)) = upperDeparture m P w r := by
  unfold upperDeparture
  rw [laneAlpha_periodic]
  exact (classPhaseAtRank_congr P w _ (sameClass_laneCell_add_m m _ r)).symm

theorem lift_laneCell {m : Nat} (hm : 0 < m) (t r : Int) :
    Drift.lift (diagDrift m) (laneCell t r) = r / (m : Int) := by
  have hn : m ≠ 0 := by omega
  simp [Drift.lift, diagDrift, laneCell, hn]

theorem liftStep_lane_east {m : Nat} (hm : 0 < m) (t r : Int) :
    Drift.liftStep (diagDrift m) (laneCell t r) .east =
      (r + 1) / (m : Int) - r / (m : Int) := by
  have hs := Drift.lift_move (diagDrift_ne_zero hm) (laneCell t r) .east
  rw [move_laneCell_east, lift_laneCell hm, lift_laneCell hm] at hs
  omega

theorem liftStep_lane_south {m : Nat} (hm : 0 < m) (t r : Int) :
    Drift.liftStep (diagDrift m) (laneCell t r) .south = 0 := by
  have hs := Drift.lift_move (diagDrift_ne_zero hm) (laneCell t r) .south
  rw [move_laneCell_south, lift_laneCell hm, lift_laneCell hm] at hs
  omega

/-- Stable time along the E,S bridge, including both phase and spatial seams.
Integer lane indices keep the lift correction explicit before taking residues. -/
theorem upper_bridge_time {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Int) :
    Drift.stableTime (diagDrift m) P w (upperArrival m P w (r + 1)) -
      Drift.stableTime (diagDrift m) P w (upperDeparture m P w r) =
      2 - (P : Int) * ((r + 1) / (m : Int) - r / (m : Int)) := by
  obtain ⟨hbdir, htmem, htdir, hsucc⟩ := upper_bridge h hm hd ht r
  obtain ⟨hbP, hbc⟩ := Drift.mem_classPhases.mp (upperDeparture_mem h hm hd ht r)
  obtain ⟨htP, htc⟩ := Drift.mem_classPhases.mp htmem
  have hb := Drift.successor_stableTime_of_class hd (diagDrift_ne_zero hm) hbP hbc hbdir
  have htop := Drift.successor_stableTime_of_class hd (diagDrift_ne_zero hm) htP htc htdir
  rw [liftStep_lane_east hm] at hb
  rw [liftStep_lane_south hm, Int.mul_zero, Int.sub_zero, hsucc] at htop
  omega

/-- Within-lane upper arrival time minus upper departure time. -/
def laneDelta (m P : Nat) (w : Nat -> Bool) (r : Nat) : Int :=
  Drift.stableTime (diagDrift m) P w (upperArrival m P w (r : Int)) -
    Drift.stableTime (diagDrift m) P w (upperDeparture m P w (r : Int))

private theorem winding_partial_sum {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (n : Nat) :
    ((List.range n).map (laneDelta m P w)).sum =
      2 * (n : Int) + Drift.stableTime (diagDrift m) P w (upperArrival m P w 0) -
        Drift.stableTime (diagDrift m) P w (upperArrival m P w (n : Int)) -
        (P : Int) * ((n : Int) / (m : Int)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Int.add_zero, ih]
    have hb := upper_bridge_time h hm hd ht (n : Int)
    simp only [Int.mul_sub] at hb
    simp only [laneDelta, Int.natCast_add, Int.natCast_one]
    omega

/-- The global winding identity. All bridge and lift facts are consequences
of consistency, full diagonal drift, and top occupancy. -/
theorem winding_identity {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) :
    ((List.range m).map (laneDelta m P w)).sum = 2 * (m : Int) - (P : Int) := by
  have hs := winding_partial_sum h hm hd ht m
  have hp : upperArrival m P w (m : Int) = upperArrival m P w 0 := by
    simpa only [Int.zero_add] using upperArrival_periodic m P w 0
  rw [hp, Int.ediv_self (show (m : Int) ≠ 0 by omega), Int.mul_one] at hs
  omega

theorem late_lane_delta_pos {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (ht : TopOccupied m P w) (r : Nat)
    (ha : laneAlpha m P w (topLayer P w - 1) (r : Int) = word001 \/
      laneAlpha m P w (topLayer P w - 1) (r : Int) = word0010) :
    0 < laneDelta m P w r := by
  have htime := rank_zero_time_lt_rank_two hm hd (laneCell (topLayer P w - 1) (r : Int))
    (first_inner_length_gt_two h hm hd ht (r : Int))
  rcases ha with ha | ha
  all_goals
    unfold laneDelta upperArrival upperDeparture
    rw [ha]
    change 0 <
      Drift.stableTime (diagDrift m) P w
        (classPhaseAtRank (diagDrift m) P w (laneCell (topLayer P w - 1) (r : Int)) 2) -
      Drift.stableTime (diagDrift m) P w
        (classPhaseAtRank (diagDrift m) P w (laneCell (topLayer P w - 1) (r : Int)) 0)
    omega

/-- An occupied top layer forces an upper arrival of rank zero in at least
one first-inner lane, for every chosen period and positive diagonal multiple. -/
theorem exists_rank_zero_lane {m P : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : 0 < m)
    (hd : wordDrift P w = diagDrift m) (ht : TopOccupied m P w) :
    ∃ r : Nat, r < m /\
      (laneAlpha m P w (topLayer P w - 1) (r : Int) = word100 \/
       laneAlpha m P w (topLayer P w - 1) (r : Int) = word1000) := by
  apply early_of_negative_sum m _ (laneDelta m P w)
  · intro r _ hne
    have hlate : laneAlpha m P w (topLayer P w - 1) (r : Int) = word001 \/
        laneAlpha m P w (topLayer P w - 1) (r : Int) = word0010 := by
      rcases first_inner_candidates h hm hd ht (r : Int) with ha | ha | ha | ha
      · exact False.elim (hne (Or.inl ha))
      · exact False.elim (hne (Or.inr ha))
      · exact Or.inl ha
      · exact Or.inr ha
    have hp := late_lane_delta_pos h hm hd ht r hlate
    omega
  · rw [winding_identity h hm hd ht]
    have hp := strict_period_bound h hd
    omega

end LangtonsAnt.DiagonalWinding
