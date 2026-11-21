import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2113 : checkSingleBlackFast (-84, -62) 20171 .east (32, 26) (-1, -44) = true := by
  decide +kernel

end LangtonsAnt
