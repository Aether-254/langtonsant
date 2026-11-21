import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0083 : checkSingleBlackFast (6, -4) 7724 .north (0, 2) (-16, -10) = true := by
  decide +kernel

end LangtonsAnt
