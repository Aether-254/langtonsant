import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2096 : checkSingleBlackFast (-82, -61) 20757 .east (32, 22) (16, -55) = true := by
  decide +kernel

end LangtonsAnt
