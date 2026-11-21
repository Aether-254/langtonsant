import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2208 : checkSingleBlackFast (-90, -72) 30123 .east (48, 36) (7, -58) = true := by
  decide +kernel

end LangtonsAnt
