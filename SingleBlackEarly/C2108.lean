import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2108 : checkSingleBlackFast (-83, -58) 22103 .east (44, 23) (-2, -62) = true := by
  decide +kernel

end LangtonsAnt
