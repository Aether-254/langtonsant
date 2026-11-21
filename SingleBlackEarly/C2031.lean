import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2031 : checkSingleBlackFast (-74, -55) 21648 .north (39, 35) (-65, -27) = true := by
  decide +kernel

end LangtonsAnt
