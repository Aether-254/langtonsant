import Phase49P1

/-! Heavy kernel check of `Phase49Blank`, in its own module so that its memory is released. -/

namespace LangtonsAnt
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem checkBlankJunk_true : checkBlankJunk = true := by
  decide +kernel

end LangtonsAnt
