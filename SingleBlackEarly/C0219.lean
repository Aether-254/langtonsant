import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0219 : checkSingleBlackFast (11, 7) 2719 .east (-6, -9) (-14, 0) = true := by
  decide +kernel

end LangtonsAnt
