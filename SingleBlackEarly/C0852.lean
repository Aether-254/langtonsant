import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0852 : checkSingleBlackFast (-7, 10) 6735 .east (-4, -3) (-18, -16) = true := by
  decide +kernel

end LangtonsAnt
