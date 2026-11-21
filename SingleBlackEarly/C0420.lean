import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0420 : checkSingleBlackFast (16, 1) 5546 .south (-8, -5) (-21, -4) = true := by
  decide +kernel

end LangtonsAnt
