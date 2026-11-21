import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0282 : checkSingleBlackFast (15, 11) 5288 .north (0, -4) (-18, -8) = true := by
  decide +kernel

end LangtonsAnt
