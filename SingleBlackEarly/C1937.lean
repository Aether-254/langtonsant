import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1937 : checkSingleBlackFast (-68, -46) 19339 .east (24, 18) (-9, -36) = true := by
  decide +kernel

end LangtonsAnt
