import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0122 : checkSingleBlackFast (5, 7) 3767 .east (-8, -13) (-16, -6) = true := by
  decide +kernel

end LangtonsAnt
