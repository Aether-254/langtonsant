import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0089 : checkSingleBlackFast (5, 4) 6106 .south (-9, 8) (-22, 1) = true := by
  decide +kernel

end LangtonsAnt
