import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0553 : checkSingleBlackFast2 (16, -7) 16809 .east (-6, -9) (-19, -17) = true := by
  decide +kernel

end LangtonsAnt
