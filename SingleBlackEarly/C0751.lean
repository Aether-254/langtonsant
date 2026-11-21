import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0751 : checkSingleBlackFast (23, -13) 6382 .south (-17, 1) (-22, 0) = true := by
  decide +kernel

end LangtonsAnt
