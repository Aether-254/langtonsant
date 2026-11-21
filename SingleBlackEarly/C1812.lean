import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1812 : checkSingleBlackFast (-54, -36) 28251 .east (30, 18) (-11, -40) = true := by
  decide +kernel

end LangtonsAnt
