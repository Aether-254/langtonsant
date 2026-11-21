import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2197 : checkSingleBlackFast (-92, -67) 19579 .east (34, 37) (12, -54) = true := by
  decide +kernel

end LangtonsAnt
