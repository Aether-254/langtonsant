import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1497 : checkSingleBlackFast (-28, -6) 25827 .east (0, -14) (-33, -8) = true := by
  decide +kernel

end LangtonsAnt
