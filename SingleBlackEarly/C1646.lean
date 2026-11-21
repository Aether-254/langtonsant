import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1646 : checkSingleBlackFast (-41, -16) 19919 .east (23, 1) (-22, -41) = true := by
  decide +kernel

end LangtonsAnt
