import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0005 : checkSingleBlackFast (-1, 1) 1006 .north (2, 2) (-9, -3) = true := by
  decide +kernel

end LangtonsAnt
