import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0453 : checkSingleBlackFast (18, 10) 6164 .south (-13, -2) (-21, 0) = true := by
  decide +kernel

end LangtonsAnt
