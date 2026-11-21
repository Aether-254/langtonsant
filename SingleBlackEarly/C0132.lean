import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0132 : checkSingleBlackFast2 (6, -1) 12683 .east (-10, -5) (-14, -24) = true := by
  decide +kernel

end LangtonsAnt
