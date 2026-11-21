import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2196 : checkSingleBlackFast (-91, -66) 22519 .east (48, 27) (2, -66) = true := by
  decide +kernel

end LangtonsAnt
