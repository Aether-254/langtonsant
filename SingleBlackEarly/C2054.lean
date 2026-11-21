import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2054 : checkSingleBlackFast (-76, -58) 29395 .east (41, 29) (0, -51) = true := by
  decide +kernel

end LangtonsAnt
