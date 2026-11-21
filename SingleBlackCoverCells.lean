import SingleBlackEarly.Cells
import SingleBlackCover

/-! Every cell the blank orbit visits before time 13952 is one of the certified early cells. -/

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem earlyCells_inWide : earlyCells.all (fun p => decide (InWide p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem earlyCells_cover_check : checkBlankCover (wideCells earlyCells) 13952 wideBlank = true := by
  decide +kernel

theorem earlyCells_cover (j : Nat) (hj : j < 13952) : (run blank j).pos ∈ earlyCells :=
  blank_cover_of_check earlyCells_inWide earlyCells_cover_check j hj

end LangtonsAnt
