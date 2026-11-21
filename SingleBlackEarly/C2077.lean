import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2077 : checkSingleBlackFast (-79, -60) 76585 .east (43, 24) (-74, 8) = true := by
  decide +kernel

end LangtonsAnt
