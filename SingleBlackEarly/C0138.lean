import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0138 : checkSingleBlackFast (7, 1) 9131 .east (-6, -17) (-24, -4) = true := by
  decide +kernel

end LangtonsAnt
