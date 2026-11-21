import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0266 : checkSingleBlackFast (13, 7) 4155 .east (-5, -9) (-14, -1) = true := by
  decide +kernel

end LangtonsAnt
