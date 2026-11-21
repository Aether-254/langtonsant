import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2076 : checkSingleBlackFast (-78, -60) 29499 .east (42, 30) (1, -52) = true := by
  decide +kernel

end LangtonsAnt
