import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0147 : checkSingleBlackFast (6, 3) 3904 .north (2, -3) (-16, -3) = true := by
  decide +kernel

end LangtonsAnt
