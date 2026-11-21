import HighwayEntrance

namespace LangtonsAnt

theorem blank_tail_bounded (n : Nat) : weight (run blank (12080 + n)).pos <= -86 := by
  have c := highwaySeed_certificate.translate (-56, -30)
  have he : AgreesBelow (0 + weight (-56, -30)) (run blank 12080)
      (translate (-56, -30) highwaySeed.toState) := blank_entry
  have hm := c.matches_forever he n
  have hb := c.all_bounded n
  rw [← hm.pos, ← run_add] at hb
  exact hb

/-- A sufficient global bound, with no claim that 126 is optimal. -/
theorem blank_all_bounded (n : Nat) : weight (run blank n).pos <= 126 := by
  by_cases hn : n < 12080
  · have hbox := checkPackedEntry_inBox blank_entry_check n hn
    rw [packedBlank_toState] at hbox
    simp only [InBox] at hbox
    unfold weight
    omega
  · have hb := blank_tail_bounded (n - 12080)
    have heq : 12080 + (n - 12080) = n := by omega
    rw [heq] at hb
    omega

/-- Any coloring outside this half-plane is invisible to the entire blank trajectory. -/
theorem blank_trace_of_white_below {s : State}
    (hp : s.pos = (0, 0)) (hd : s.dir = .north)
    (hw : forall p, weight p <= 126 -> s.board p = false) (n : Nat) :
    (run s n).pos = (run blank n).pos ∧
    (run s n).dir = (run blank n).dir ∧ readColor s n = readColor blank n := by
  have h : AgreesBelow 126 s blank := ⟨hp, hd, hw⟩
  have hm := h.run n (fun j _ => blank_all_bounded j)
  refine ⟨hm.pos, hm.dir, ?_⟩
  unfold readColor
  rw [hm.pos]
  exact hm.board _ (blank_all_bounded n)

/-- This initial-state family allows arbitrarily many black cells at unbounded coordinates. -/
theorem standard_of_white_below {s : State}
    (hp : s.pos = (0, 0)) (hd : s.dir = .north)
    (hw : forall p, weight p <= 126 -> s.board p = false) :
    StandardHighwayFrom s 12080 (-2, -2) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    have h0 := blank_trace_of_white_below hp hd hw n
    have h1 := blank_trace_of_white_below hp hd hw (n + 104)
    simpa only [h0.1, h0.2.1, h1.1, h1.2.1] using blank_highway n hn
  · intro n
    exact (blank_trace_of_white_below hp hd hw (12080 + n)).2.2.trans (blank_standard.2 n)

theorem standard_of_separated_black_cells (s : FiniteState)
    (hp : s.pos = (0, 0)) (hd : s.dir = .north)
    (hb : forall p, p ∈ s.black -> 126 < weight p) :
    StandardHighwayFrom s.toState 12080 (-2, -2) := by
  apply standard_of_white_below hp hd
  intro p hweight
  have hnot : p ∉ s.black := by
    intro hm
    have := hb p hm
    omega
  simp [FiniteState.toState, hnot]

theorem standard_of_white_in_frame {s : State}
    (hw : forall p, weight p <= 126 -> (normalize s.dir s.pos s).board p = false) :
    StandardHighwayFrom s 12080 (rotatePoint s.dir (-2, -2)) := by
  have hp := normalize_pose_at_self s
  have hs := standard_of_white_below hp.1 hp.2 hw
  have hh := (hs.rotate s.dir).translate s.pos
  change StandardHighwayFrom (pose s.dir s.pos (normalize s.dir s.pos s)) 12080 _ at hh
  rw [pose_normalize] at hh
  exact hh

end LangtonsAnt
