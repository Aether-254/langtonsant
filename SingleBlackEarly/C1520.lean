import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1520 : checkSingleBlackFast (-31, -8) 28264 .north (9, 13) (-9, -39) = true := by
  decide +kernel

end LangtonsAnt
