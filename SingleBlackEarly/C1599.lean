import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1599 : checkSingleBlackFast (-38, -12) 11484 .north (8, 0) (-34, -16) = true := by
  decide +kernel

end LangtonsAnt
