import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2162 : checkSingleBlackFast (-88, -67) 21069 .east (35, 25) (19, -58) = true := by
  decide +kernel

end LangtonsAnt
