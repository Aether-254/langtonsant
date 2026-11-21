import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1518 : checkSingleBlackFast2 (-30, -6) 12851 .west (2, 12) (-31, -8) = true := by
  decide +kernel

end LangtonsAnt
