import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0253 : checkSingleBlackFast (12, 9) 8186 .north (6, -4) (-21, -15) = true := by
  decide +kernel

end LangtonsAnt
