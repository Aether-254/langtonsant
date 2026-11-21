import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0704 : checkSingleBlackFast (20, -7) 5446 .south (-13, -2) (-18, -3) = true := by
  decide +kernel

end LangtonsAnt
