import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0162 : checkSingleBlackFast (-1, 7) 3238 .north (1, -3) (-18, -6) = true := by
  decide +kernel

end LangtonsAnt
