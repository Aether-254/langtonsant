import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0021 : checkSingleBlackFast (1, -3) 648 .north (4, 4) (-6, -2) = true := by
  decide +kernel

end LangtonsAnt
