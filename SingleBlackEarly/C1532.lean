import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1532 : checkSingleBlackFast2 (-32, -4) 15641 .west (9, 15) (-35, -8) = true := by
  decide +kernel

end LangtonsAnt
