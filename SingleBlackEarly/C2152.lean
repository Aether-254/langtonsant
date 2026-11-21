import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2152 : checkSingleBlackFast (-87, -62) 22311 .east (46, 25) (0, -64) = true := by
  decide +kernel

end LangtonsAnt
