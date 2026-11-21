import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2091 : checkSingleBlackFast (-82, -60) 20067 .east (31, 25) (-2, -43) = true := by
  decide +kernel

end LangtonsAnt
