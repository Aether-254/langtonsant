import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0348 : checkSingleBlackFast (-5, 13) 5025 .east (1, -11) (-17, -14) = true := by
  decide +kernel

end LangtonsAnt
