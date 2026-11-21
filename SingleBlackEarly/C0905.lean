import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0905 : checkSingleBlackFast (-11, 9) 9976 .north (7, 3) (-31, -13) = true := by
  decide +kernel

end LangtonsAnt
