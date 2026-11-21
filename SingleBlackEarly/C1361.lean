import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1361 : checkSingleBlackFast (-15, 4) 19455 .east (-5, -14) (-33, -5) = true := by
  decide +kernel

end LangtonsAnt
