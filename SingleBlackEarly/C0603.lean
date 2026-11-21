import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0603 : checkSingleBlackFast2 (15, 13) 15170 .south (-15, 0) (-30, -13) = true := by
  decide +kernel

end LangtonsAnt
