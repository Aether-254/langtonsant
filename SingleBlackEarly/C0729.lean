import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0729 : checkSingleBlackFast (13, -12) 8754 .south (-8, -3) (-21, -8) = true := by
  decide +kernel

end LangtonsAnt
