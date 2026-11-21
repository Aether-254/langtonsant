import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0210 : checkSingleBlackFast (8, 4) 6906 .north (1, -4) (-18, -13) = true := by
  decide +kernel

end LangtonsAnt
