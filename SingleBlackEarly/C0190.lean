import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0190 : checkSingleBlackFast (11, 0) 4753 .east (-2, -6) (-16, -5) = true := by
  decide +kernel

end LangtonsAnt
