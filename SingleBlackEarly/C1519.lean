import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1519 : checkSingleBlackFast (-30, -8) 20435 .east (3, -6) (-5, -33) = true := by
  decide +kernel

end LangtonsAnt
