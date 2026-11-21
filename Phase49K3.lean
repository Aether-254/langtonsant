import Phase49P3

/-! Heavy kernel check of `Phase49Blank`, in its own module so that its memory is released. -/

namespace LangtonsAnt
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem y49_run_check :
    checkWideGuardEntry y49Guard (-45) (highwaySeed.translate (-30, -15)) y49Delay
      Y49Frame.toWide = true := by
  decide +kernel

end LangtonsAnt
