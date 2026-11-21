import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2069 : checkSingleBlackFast (-80, -58) 19963 .east (30, 24) (-3, -42) = true := by
  decide +kernel

end LangtonsAnt
