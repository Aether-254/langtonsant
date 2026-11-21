import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2151 : checkSingleBlackFast (-89, -61) 26257 .east (40, 28) (18, -63) = true := by
  decide +kernel

end LangtonsAnt
