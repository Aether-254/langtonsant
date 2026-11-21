import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1566 : checkSingleBlackFast (-33, -12) 29189 .east (6, -7) (-9, -35) = true := by
  decide +kernel

end LangtonsAnt
