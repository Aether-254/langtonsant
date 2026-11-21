import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0395 : checkSingleBlackFast (10, -4) 8480 .north (-7, 7) (-21, -3) = true := by
  decide +kernel

end LangtonsAnt
