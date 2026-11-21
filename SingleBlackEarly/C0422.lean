import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0422 : checkSingleBlackFast (18, 1) 9987 .east (-4, 0) (-21, -20) = true := by
  decide +kernel

end LangtonsAnt
