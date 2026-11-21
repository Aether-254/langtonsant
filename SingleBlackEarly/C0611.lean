import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0611 : checkSingleBlackFast (3, -7) 6627 .east (-1, -6) (-15, -17) = true := by
  decide +kernel

end LangtonsAnt
