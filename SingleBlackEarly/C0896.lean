import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0896 : checkSingleBlackFast (-9, 10) 9971 .east (4, -6) (-21, -24) = true := by
  decide +kernel

end LangtonsAnt
