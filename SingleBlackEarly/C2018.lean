import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2018 : checkSingleBlackFast (-77, -50) 19666 .north (30, 23) (-57, -36) = true := by
  decide +kernel

end LangtonsAnt
