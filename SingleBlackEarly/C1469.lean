import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1469 : checkSingleBlackFast (-27, 1) 13103 .east (5, -3) (-22, -17) = true := by
  decide +kernel

end LangtonsAnt
