import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0708 : checkSingleBlackFast2 (0, -8) 11120 .south (-14, -1) (-24, -13) = true := by
  decide +kernel

end LangtonsAnt
