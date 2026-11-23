import DelayedHighway

namespace LangtonsAnt.PersistA.EntryBridge

theorem north_black_after_white_east_entry (s : State)
    (hd : s.dir = .east) (hc : s.board s.pos = false) :
    (step s).dir = .south ∧
    move (step s).pos .north = s.pos ∧
    (step s).board (move (step s).pos .north) = true := by
  simp [step, hd, hc, turn, Direction.right, move, flip]

theorem first_north_read_black (s : State) (n : Nat)
    (hd : s.dir = .east) (hc : s.board s.pos = false)
    (hfirst : ∀ j, j < n -> (run (step s) j).pos ≠ move (step s).pos .north)
    (hpos : (run (step s) n).pos = move (step s).pos .north) :
    (run (step s) n).board (run (step s) n).pos = true := by
  rw [hpos, board_unchanged_of_avoids (step s) _ n hfirst]
  exact (north_black_after_white_east_entry s hd hc).2.2


end LangtonsAnt.PersistA.EntryBridge
