import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0285 : checkSingleBlackFast (14, 11) 20027 .east (-16, -16) (-23, -10) = true := by
  decide +kernel

end LangtonsAnt
