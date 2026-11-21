import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0592 : checkSingleBlackFast (20, 12) 7500 .north (-9, 7) (-1, -19) = true := by
  decide +kernel

end LangtonsAnt
