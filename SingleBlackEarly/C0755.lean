import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0755 : checkSingleBlackFast (22, -11) 10766 .south (-18, 3) (-29, -12) = true := by
  decide +kernel

end LangtonsAnt
