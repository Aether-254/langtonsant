import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0960 : checkSingleBlackFast (5, 18) 7875 .east (-6, -7) (-22, -10) = true := by
  decide +kernel

end LangtonsAnt
