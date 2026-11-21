import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2153 : checkSingleBlackFast (-88, -63) 19371 .east (32, 35) (10, -52) = true := by
  decide +kernel

end LangtonsAnt
