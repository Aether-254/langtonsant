import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2092 : checkSingleBlackFast (-83, -60) 20789 .east (39, 24) (16, -58) = true := by
  decide +kernel

end LangtonsAnt
